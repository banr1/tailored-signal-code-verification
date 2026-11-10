/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMapBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDropBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.ComposeBudget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget

/-!
# Budget-Threaded Relocatable `MessageEncrypt` Hooks, Callees, and Segment Specifications

Re-exports the budget-threaded envelopes, seam states, and `_with_stores` contract from
`PlacedDefsBudgetAux` for block `198` (`lsProg_198 H`), and defines `PublicApiEncHooksPlaced`,
`EncCalleesPlaced`, `EncEnvPlaced`, `SegExitPlaced`, and the nine segment specifications under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (durationSinceBudgetSpec timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (cmDropSpec kyberMapSpec preKeyMsgNewSpec)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (OtrEncryptEnv SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (remoteIdentityKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget
  (otrApplyPlacedSpec otrApply_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget
  (otrFromPlacedSpec otrFromRawPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget (otrFrom_placed_ok)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (EncFsCtxPlaced RecordInScopeEnc StepsThroughEncrypt WithStoresEncGhost encEntryPlaced
   fromSessionState_pqrState lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym
   lsStringCloneSym lsTimeAddSym storedRecord)

export PlacedDefsBudgetAux
  (FromApplyEnv FromSaveEnv FromCmEnv pendingKyberPayload preKeyMsgFromItems)
export PlacedDefsBudgetAux
  (PreKeyPostEncryptEnv FromKeyEnv FromOtrEnv FromCurEnv WithStoresEncEnv)
export PlacedDefsBudgetAux
  (storeFinal_retag idFinal_retag encStoreExtraPlaced_retag
   withStoresEncPlacedSpecV withStoresEncBudgetSpecV)
export PlacedDefsBudgetAux
  (withStoresEncPlacedSpecV_pre_addrOk CurStateVPlaced CurStateVBudget
   OtrStateVPlaced OtrStateVBudget)
export PlacedDefsBudgetAux
  (KeyStateVPlaced KeyStateVBudget CmStateVPlaced CmStateVBudget SaveStateVPlaced)
export PlacedDefsBudgetAux
  (SaveStateVBudget ApplyStateVPlaced ApplyStateVBudget StoredStateVPlaced StoredStateVBudget)
export PlacedDefsBudgetAux
  (fromCurEnv_phaseCreditSpec withStoresEncEnv_fitsEnv_witness)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. External Hooks and Callees on `lsProg_198 H` -/

/-- External hook contracts and panic stubs on `H : LibsignalHooks` used by Block `198`
    (`session_message_encrypt_with_stores`) and its 8 proved placed callees under
    `RustCliAllocBudget M`. -/
structure PublicApiEncHooksPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)
  memcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneBudgetSpec M A lim)
  timeAdd : HookSat H lsTimeAddSym timeAddBudgetSpec
  durationSince : HookSat H lsDurationSinceSym durationSinceBudgetSpec
  handleError : H lsHandleErrorSym = some Rust.panicked
  handleAllocError : H lsHandleAllocErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

abbrev PublicApiEncHooksBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  PublicApiEncHooksPlaced A lim H

/-- Budget-threaded relocatable `OTR::encrypt::<HookRng>` raw spec (`onOom = ⌜False⌝`,
    `allocFailedIn` eliminated from `onPanic`). -/
def otrEncryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidParse x)⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrEncryptEnv C S sendEnv uuidParse x evs⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

abbrev otrEncryptBudgetSpec := @otrEncryptPlacedSpec

/-- Budget-threaded relocatable `OTR::encrypt::<HookRng>` spec restricted to OTRs whose SPQR state
    satisfies `Q`. -/
def otrEncryptPlacedSpecQ [LibsignalPlacement] {M : AllocCostModel} (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  { otrEncryptPlacedSpec C A lim ctl parse S sendEnv with
    pre := fun (x, st) s =>
      ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
        (CryptoVerification.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ
          Q C (A.atState lim st s) ctl parse S).pre x s }

abbrev otrEncryptBudgetSpecQ := @otrEncryptPlacedSpecQ

/-- Budget-threaded relocatable `OTR::encrypt::<HookRng>` spec for OTRs whose `(pqrState, rest)`
    satisfies `Q`, with `F` framed. -/
def otrEncryptPlacedSpecQF [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  { otrEncryptPlacedSpec C A lim ctl parse S sendEnv with
    pre := fun (x, st) s =>
      ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
        (CryptoVerification.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF
          Q F C (A.atState lim st s) ctl parse S).pre x s
    post := fun (x, st) s0 sf =>
      F ∗ (otrEncryptPlacedSpec C A lim ctl parse S sendEnv).post (x, st) s0 sf }

abbrev otrEncryptBudgetSpecQF := @otrEncryptPlacedSpecQF

/-- Bundle of all 9 in-library callees invoked by Block `198` (`lsProg_198 H`) under
    `[LibsignalPlacement]` and `RustCliAllocBudget M`. -/
structure EncCalleesPlaced [LibsignalPlacement] {M : AllocCostModel} (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (H : LibsignalHooks) : Prop where
  otrFrom : subroutine_ok (lsProg_198 H) (lsmpl.base 19)
    (StoreKit.withLsRoCl lsmpl (otrFromRawPlacedSpec M A lim))
  otrApply : subroutine_ok (lsProg_198 H) (lsmpl.base 20)
    (StoreKit.withLsRoCl lsmpl (otrApplyPlacedSpec M A lim))
  remoteIk : subroutine_ok (lsProg_198 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc))
  otrEnc : subroutine_ok (lsProg_198 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
    (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ Q C A lim ctl parse S sendEnv))
  unack : subroutine_ok (lsProg_198 H) (lsmpl.base 36)
    (StoreKit.withLsRoCl lsmpl (CalleeProofs.UnackItemsBudget.unackItemsPlacedSpec A.repAlloc))
  kyber : subroutine_ok (lsProg_198 H) (lsmpl.base 127)
    (StoreKit.withLsRoCl lsmpl (kyberMapSpec M A lim))
  psmNew : subroutine_ok (lsProg_198 H) (lsmpl.base 41)
    (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec M A lim))
  cmDrop : subroutine_ok (lsProg_198 H) (lsmpl.base 135)
    (StoreKit.withLsRoCl lsmpl (cmDropSpec M A lim))
  dropSs : subroutine_ok (lsProg_198 H) (lsmpl.base 139)
    (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2Spec M A lim))

abbrev EncCalleesBudget := @EncCalleesPlaced

private theorem hookSat_noAllocShim_of_sessionShimBudget
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym sessionShimBudgetSpec) :
    HookSat H sym (withVmPreserved noAllocShimSpec) := by
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
    (h : subroutine_ok prog entry (otrFromPlacedSpec M A lim)) :
    subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (otrFromRawPlacedSpec M A lim)) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [otrFromPlacedSpec, OutgoingRatchet.withLsRoLoaded, withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hfr.2, ?_⟩
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Discharge all 8 proved in-library callees of `EncCalleesPlaced` from
    `PublicApiEncHooksPlaced A lim H`, leaving only `otrEnc` as an assumption. -/
theorem EncCalleesPlaced.of_otrEnc [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {H : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A lim H)
    (hotrEnc : subroutine_ok (lsProg_198 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ Q C A lim ctl parse S sendEnv))) :
    EncCalleesPlaced Q C A lim ctl parse S sendEnv H where
  otrFrom :=
    StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := lsProg_198 H)
      (subroutine_ok_withLsCodeRoLoaded_of_otrFromPlaced
        (otrFrom_placed_ok hhooks.dealloc
          (((Getters.instIsLsBlockProg_29 H).eq_blockProgram.trans
              (CryptoVerification.instIsLsBlockProg_29 H).eq_blockProgram.symm) ▸
            LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok
              A.repAlloc H)
          (((Getters.instIsLsBlockProg_5 H).eq_blockProgram.trans
              (CryptoVerification.instIsLsBlockProg_5 H).eq_blockProgram.symm) ▸
            LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget.drop_spe_placed_ok
              hhooks.dealloc)))
  otrApply :=
    StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_198 H)
      (otrApply_placed_ok (hookSat_noAllocShim_of_sessionShimBudget hhooks.shim)
        hhooks.alloc hhooks.dealloc)
  remoteIk :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok
        A.repAlloc H)
  otrEnc := hotrEnc
  unack :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (CalleeProofs.UnackItemsBudget.unackItems_placed_ok hhooks.timeAdd)
  kyber :=
    StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_198 H)
      (CalleeProofs.KyberMapBudget.kyberMap_placed_ok hhooks.shim hhooks.alloc hhooks.memcpy)
  psmNew :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (PreKeySignalMessageNew.ComposeBudget.preKeyMsgNew_placed_ok_sessionHooks
        hhooks.shim hhooks.alloc hhooks.dealloc hhooks.realloc hhooks.memcpy)
  cmDrop :=
    StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_198 H)
      (CalleeProofs.CmDropBudget.cmDrop_placed_ok hhooks.dealloc)
  dropSs :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget.drop_session_structure_local2_placed_ok
        hhooks.dealloc)

/-! ## 2. Segment Environment, Exit Relation, and Segment Specifications -/

/-- Relocatable budget-threaded environment of every `MessageEncrypt` segment on `lsProg_198 H`. -/
structure EncEnvPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  hooks : PublicApiEncHooksPlaced A lim H
  kitOk : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H
  ikitOk : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H
  callees : EncCalleesPlaced Q C A lim ctl parse S sendEnv H
  vtables : SessionOnlyVtablesPlacedOk kit
  idVtables : IdentityVtablesPlacedOk ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → Q s.state.pqRatchetState
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

abbrev EncEnvBudget := @EncEnvPlaced

theorem EncEnvPlaced.q_otr [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (env : EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- Budget-threaded segment exit relation on `lsProg_198 H` under `[LibsignalPlacement]`. -/
def SegExitPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (lsProg_198 H).CodeLoaded s.mem →
    ∃ sf, Steps (lsProg_198 H) s sf ∧
      (next sf ∨
        SubroutineOutcome
          (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
            C ctl parse S sendEnv encRecord)
          (x, st_init) R s0 sf)

abbrev SegExitBudget := @SegExitPlaced

theorem SegExitPlaced.next [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem SegExitPlaced.of_false [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h : SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False)) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hsteps, Or.inr hout⟩

theorem SegExitPlaced.step_left [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s sm : State}
    {next : State → Prop} (hsteps : Steps (lsProg_198 Hk) s sm)
    (h : SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 sm next) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps', hout⟩ := h (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem SegExitPlaced.of_sepWP [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (lsProg_198 Hk) mid s P post)
    (hcont : ∀ sm Pm, (lsProg_198 Hk).CodeLoaded s.mem →
      Steps (lsProg_198 Hk) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R0 s0 sm next) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem SegExitPlaced.call {α : Type} [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_198 Hk) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (lsProg_198 Hk) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl parse S sendEnv encRecord).onPanic (x, st_init) s0 sf ∗ R0))
    (hnext : ∀ sm : State, (lsProg_198 Hk).CodeLoaded s.mem →
      Steps (lsProg_198 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  have hwpp : SepWPp (lsProg_198 Hk) ret_pc s (spec.pre xc s ∗ F)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post xc s sm ∗ F)
      (fun sf Pf => Pf = spec.onPanic xc s sf ∗ F) :=
    SepWPp.call (x := xc) (F := F) hcall hpc hrun hsp hlr
      (fun _ h => by rwa [sepConj_assoc] at h) hexit (fun _ _ => rfl)
      (fun _ hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hst hmem => False.elim (hoom sf (F ∗ R') hst hmem))
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | ⟨hpan, _, hpost, rfl⟩ | ⟨_, hoom_f⟩⟩ :=
    hwpp R (by rwa [← sepConj_assoc] at hm) hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (not_satisfies_false_sepConj hoom_f).elim

def SegLoadSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
      EncFsCtxPlaced kit ikit H s0 s0 →
      s0.pc = encEntryPlaced → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨
        (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl parse S sendEnv encRecord).pre (x, st_init) s0 ∗ R) →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s0
        (fun s => ∃ st' r g sess,
          CurStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r g sess R s0 s)

abbrev SegLoadSpecVBudget := @SegLoadSpecVPlaced

def SegFromSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (g : RecordGhost) (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CurStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r g sess R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st' otr taken pqCap pqPtr,
          OtrStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken pqCap pqPtr R s0 s')

abbrev SegFromSpecVBudget := @SegFromSpecVPlaced

def SegIdentitySpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp)
      (s0 s : State),
      OtrStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ k,
          KeyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st r sess otr taken pqCap pqPtr k R s0 s')

abbrev SegIdentitySpecVBudget := @SegIdentitySpecVPlaced

def SegSignalSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      KeyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr k R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st' m otr' pqCap' pqPtr',
          CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s')

abbrev SegSignalSpecVBudget := @SegSignalSpecVPlaced

def SegPreKeySpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      KeyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr k R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st' m otr' pqCap' pqPtr',
          CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s')

abbrev SegPreKeySpecVBudget := @SegPreKeySpecVPlaced

def SegTrustSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' pqCap' pqPtr' R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st',
          SaveStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s')

abbrev SegTrustSpecVBudget := @SegTrustSpecVPlaced

def SegSaveSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      SaveStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' pqCap' pqPtr' R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st' c,
          ApplyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' c R s0 s')

abbrev SegSaveSpecVBudget := @SegSaveSpecVPlaced

def SegApplyStoreSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      ApplyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' pqCap' pqPtr' c R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st',
          StoredStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' c R s0 s')

abbrev SegApplyStoreSpecVBudget := @SegApplyStoreSpecVPlaced

def SegFinishSpecVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      StoredStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' c R s0 s →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)

abbrev SegFinishSpecVBudget := @SegFinishSpecVPlaced

/-- All nine budget-threaded `MessageEncrypt` segments on `lsProg_198 H` under
    `[LibsignalPlacement]`. -/
structure EncSegsVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  load : SegLoadSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  fromS : SegFromSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  identity : SegIdentitySpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  signal : SegSignalSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  preKey : SegPreKeySpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  trust : SegTrustSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  save : SegSaveSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  applyStore : SegApplyStoreSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  finish : SegFinishSpecVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H

abbrev EncSegsVBudget := @EncSegsVPlaced

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
