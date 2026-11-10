/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Assembly
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsVXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable `MessageDecrypt` Assembly

Assembles the twelve budget-threaded `[LibsignalPlacement]` segment contracts (`DecSegsVPlaced`) and
callee contracts (`DecCalleesPlaced`) into `withStoresDecPlacedSpecV` on block `197` (`lsProg_197 H`)
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageDecrypt.AssemblyBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl lsRustDeallocSym instIsLsBlockProg_139)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet.Getters (instIsLsBlockProg_29)
open CryptoVerification.LibsignalTripleRatchet.Record
  (recEntryPlaced recExitPlaced)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.Placed
  (lsProg_197 lsProg_197_eq_record_lsProg_197)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (SessionStoreSpec FsCtx KitFsOk withEnvPre withEnvPre_pre_elim
   reaches_outcome_withEnvPre subroutine_ok_of_withEnvPre ls_subroutine_ok_rocl_of_cl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (DecFsCtxPlaced ScopePq scopePq_true wsEntryPCPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (TryDecryptEnvArgs recordDecryptPlacedSpec)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (LoadPolledStateVPlaced RegionSomeStateVPlaced RegionNoneStateVPlaced
   PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced
   TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced
   ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk
   DecSegVPlaced DecHypsVPlaced RemoteIdentityKeyPlacedOk
   DropSessionStructureLocal2PlacedOk
   SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced
   SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced
   SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced
   SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The twelve budget-threaded `[LibsignalPlacement]` segment specifications on `lsProg_197 H`. -/
structure DecSegsVPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  load : SegLoadSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  dispatch : SegDispatchSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  regionSome : SegRegionSomeSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  regionNone : SegRegionNoneSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  postSome : SegPostSomeSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  postNone : SegPostNoneSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  trust : SegTrustSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  untrusted : SegUntrustedSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  save : SegSaveSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  store : SegStoreSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  errTeardown : SegErrTeardownSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope
  write : SegWriteSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope

theorem decSegsVPlaced_of_seams [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hLoad : SegLoadSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hDispatch : SegDispatchSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hRegionSome : SegRegionSomeSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hRegionNone : SegRegionNoneSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hPostSome : SegPostSomeSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hPostNone : SegPostNoneSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hTrust : SegTrustSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hUntrusted : SegUntrustedSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hSave : SegSaveSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hStore : SegStoreSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hErrTeardown : SegErrTeardownSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hWrite : SegWriteSpecVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope) :
    DecSegsVPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope :=
  ⟨hLoad, hDispatch, hRegionSome, hRegionNone, hPostSome, hPostNone, hTrust, hUntrusted,
    hSave, hStore, hErrTeardown, hWrite⟩

/-- Callee facts consumed by budget-threaded `[LibsignalPlacement]` `MessageDecrypt` segments:
the record-decrypt region (restricted to `Q` on `pqRatchetState`), `<SessionState>::remote_identity_key`
(Block `29`), and `drop_glue::<SessionStructure> [local#2]` (Block `139`). -/
structure DecCalleesPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_197 H) recEntryPlaced recExitPlaced
    ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
      (fun p => Q p.1.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A.repAlloc H
  dropSs : DropSessionStructureLocal2PlacedOk A lim H

/-- Chain a budget-threaded `[LibsignalPlacement]` segment into the rest of the run. -/
theorem decSegVPlaced_chain [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

/-- `decSegVPlaced_chain` carrying `DecFsCtxPlaced … s0` to the next seam. -/
theorem decSegVPlaced_chainFs [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h1 : DecSegVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s next)
    (h2 : ∀ s', DecFsCtxPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_197 H)
        (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s') :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

section ChainVPlaced

variable [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
  {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
  {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {H : LibsignalHooks}
  {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
  {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
  (hC : DecCalleesPlaced C A lim ctl S tdEnv H Q)
  (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
  (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

include hH hS in
theorem reachVPlaced_resultFinal (s : State)
    (h : ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s :=
  decSegVPlaced_chain (hS.write hH x st_init R s0 s h) (fun _ hf => hf.elim)

include hH hC hS in
theorem reachVPlaced_errJoin (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s :=
  decSegVPlaced_chain (hS.errTeardown hH hC.dropSs x st_init pt R s0 s h)
    (reachVPlaced_resultFinal hH hS x st_init R s0)

include hH hC hS hAddr in
theorem reachVPlaced_storeCall (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s :=
  decSegVPlaced_chain (hS.store hH hC.dropSs x st_init ans R s0 s hAddr.1 hfs h)
    (fun s' h' => h'.elim
      (reachVPlaced_resultFinal hH hS x st_init R s0 s')
      (reachVPlaced_errJoin hH hC hS x st_init R s0 true s'))

include hH hC hS hAddr in
theorem reachVPlaced_trusted (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans t R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s := by
  cases t with
  | true =>
    exact decSegVPlaced_chainFs hfs (hS.save hH x st_init ans R s0 s hAddr.2 hfs h)
      (fun s' hfs' h' => h'.elim
        (fun ⟨ans', hsc⟩ => reachVPlaced_storeCall hH hC hS x st_init R s0 hAddr ans' s' hfs' hsc)
        (reachVPlaced_errJoin hH hC hS x st_init R s0 true s'))
  | false =>
    exact decSegVPlaced_chain (hS.untrusted hH x st_init ans R s0 s h)
      (reachVPlaced_errJoin hH hC hS x st_init R s0 true)

include hH hC hS hAddr in
theorem reachVPlaced_keyReady (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s :=
  decSegVPlaced_chainFs hfs (hS.trust hH x st_init ans R s0 s hAddr.2 hfs h)
    (fun s' hfs' h' => h'.elim
      (fun ⟨ans', t, ht⟩ => reachVPlaced_trusted hH hC hS x st_init R s0 hAddr ans' t s' hfs' ht)
      (reachVPlaced_errJoin hH hC hS x st_init R s0 true s'))

include hH hC hS hAddr in
theorem reachVPlaced_loadPolled (hQ : ScopePq kit st0 Scope Q)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    reaches_outcome (lsProg_197 H)
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s := by
  refine decSegVPlaced_chainFs hfs (hS.dispatch hH x st_init ans R s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine decSegVPlaced_chainFs hfs' (hS.regionSome hH Q hC.region hQ x st_init ans R s0 s' hSome) ?_
    intro s'' hfs'' hPost
    exact decSegVPlaced_chainFs hfs'' (hS.postSome hH hC.remoteIk x st_init ans R s0 s'' hPost)
      (fun s3 hfs3 h3 => h3.elim
        (reachVPlaced_keyReady hH hC hS x st_init R s0 hAddr ans s3 hfs3)
        (reachVPlaced_errJoin hH hC hS x st_init R s0 false s3))
  · refine decSegVPlaced_chain (hS.regionNone hH x st_init ans R s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVPlaced_chain (hS.postNone hH x st_init ans R s0 s'' hPost)
      (reachVPlaced_errJoin hH hC hS x st_init R s0 false)
  · exact reachVPlaced_resultFinal hH hS x st_init R s0 s' hFin

end ChainVPlaced

/-- `session_message_decrypt_signal_with_stores` satisfies budget-threaded `withStoresDecPlacedSpecV`
with `withEnvPre` from the twelve `[LibsignalPlacement]` segments under `KitFsOk`. -/
theorem withStoresDec_placed_ok_of_segsV_fs [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hC : DecCalleesPlaced C A lim ctl S tdEnv H Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_197 H)) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withEnvPre
        (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk hpre
  have hfs0 : DecFsCtxPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegVPlaced_chainFs hfs0 (hS.load hH x st_init R s0 hfs0 hpc hrun hal hpre)
    (fun s hfs ⟨ans, h⟩ => reachVPlaced_loadPolled hH hC hS x st_init R s0 hAddr hQ ans s hfs h)

/-- `session_message_decrypt_signal_with_stores` satisfies budget-threaded `withStoresDecPlacedSpecV`
for kits with trivial `envOk`. -/
theorem withStoresDec_placed_ok_of_segsV [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hC : DecCalleesPlaced C A lim ctl S tdEnv H Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_placed_ok_of_segsV_fs hH hC hQ hS (.inl htriv))
    fun s => htriv s.fs.files

theorem remoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    RemoteIdentityKeyPlacedOk A H := by
  have _ := instIsLsBlockProg_29 H
  exact ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_197 H)
    (LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok A H)

theorem dropSessionStructureLocal2PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    DropSessionStructureLocal2PlacedOk A lim H := by
  have _ := instIsLsBlockProg_139 H
  exact ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_197 H)
    (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget.drop_session_structure_local2_placed_ok
      hDealloc)

/-- Assemble `DecCalleesPlaced` from the budget-threaded record-decrypt region contract on
`lsProg_197 H` and the proved Block `29` / Block `139` callees. -/
theorem decCalleesPlaced_of_region [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hRegion : region_ok (lsProg_197 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState))) :
    DecCalleesPlaced C A lim ctl S tdEnv H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A.repAlloc H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- Convenience bridge when `hRegion` is stated over `Record.lsProg_197 H`. -/
theorem decCalleesPlaced_of_recordRegion [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : LibsignalHooks} {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hRegion : region_ok (CryptoVerification.LibsignalTripleRatchet.Record.lsProg_197 H)
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState))) :
    DecCalleesPlaced C A lim ctl S tdEnv H Q :=
  decCalleesPlaced_of_region hDealloc (lsProg_197_eq_record_lsProg_197 H ▸ hRegion)

/-- Relocatable budget-threaded store-kit `_with_stores` decrypt with `withEnvPre`. -/
theorem decryptSignalWithStores_placed_ok_of_kit_fs [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hRegion : region_ok (lsProg_197 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun _ => True)))
    (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_197 H)) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withEnvPre
        (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_placed_ok_of_segsV_fs hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    (scopePq_true kit st0 Scope) hS hKitFs

/-- Relocatable budget-threaded store-kit `_with_stores` decrypt. -/
theorem decryptSignalWithStores_placed_ok_of_kit [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hRegion : region_ok (lsProg_197 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun _ => True)))
    (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) :=
  withStoresDec_placed_ok_of_segsV hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    (scopePq_true kit st0 Scope) hS htriv

/-- Relocatable budget-threaded `_with_stores` decrypt for an empty PQ state with `withEnvPre`. -/
theorem decryptSignalWithStoresEmpty_placed_ok_of_kit_fs [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hRegion : region_ok (lsProg_197 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => p.1.st.pqRatchetState = [])))
    (hQ : ScopePq kit st0 Scope (· = []))
    (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_197 H)) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withEnvPre
        (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_placed_ok_of_segsV_fs hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    hQ hS hKitFs

/-- Relocatable budget-threaded `_with_stores` decrypt for an empty PQ state. -/
theorem decryptSignalWithStoresEmpty_placed_ok_of_kit [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hRegion : region_ok (lsProg_197 H) recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => p.1.st.pqRatchetState = [])))
    (hQ : ScopePq kit st0 Scope (· = []))
    (hS : DecSegsVPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_197 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) :=
  withStoresDec_placed_ok_of_segsV hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    hQ hS htriv

end LibsignalBinary.Proofs.PublicApi.MessageDecrypt.AssemblyBudget
