/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Assembly
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SegmentProofsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity

/-!
# Relocatable CLI `MessageDecrypt` Assembly

Chains the twelve relocatable (`[LibsignalPlacement]`) `MessageDecrypt` segments on `lsProg_463`
into `withStoresDec_placed_ok_of_segsV` and store-kit-parameterized `decryptSignalWithStores_placed_ok_of_kit`
coroutines.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding DecCalleesPlaced decSegVPlaced_chain decSegVPlaced_chainFs reachVPlaced_resultFinal reachVPlaced_errJoin reachVPlaced_storeCall reachVPlaced_trusted reachVPlaced_keyReady reachVPlaced_loadPolled withStoresDec_placed_ok_of_segsV_fs withStoresDec_placed_ok_of_segsV remoteIdentityKeyPlacedOk dropSessionStructureLocal2PlacedOk decCalleesPlaced_of_region decCalleesPlaced_of_recordRegion decryptSignalWithStores_placed_ok_of_kit_fs decryptSignalWithStores_placed_ok_of_kit decryptSignalWithStoresEmpty_placed_ok_of_kit_fs decryptSignalWithStoresEmpty_placed_ok_of_kit lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain segLoadVPlaced_ok segDispatchVPlaced_ok segRegionSomeVPlaced_ok segRegionNoneVPlaced_ok segPostSomeVPlaced_ok segPostNoneVPlaced_ok segTrustVPlaced_ok segUntrustedVPlaced_ok segSaveVPlaced_ok segStoreVPlaced_ok segErrTeardownVPlaced_ok segWriteVPlaced_ok recordSplit_placed_ok recordJoin_placed_ok DecSegsVPlaced decSegsVPlaced_of_seams decSegsVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
variable {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {Scope : SessionRecord (List (BitVec 8)) → Prop}


open CryptoVerification

/-- Callee contracts required alongside `DecHypsVPlaced`: the record-decrypt region restricted to `Q`
on `pqRatchetState`, `<SessionState>::remote_identity_key`, and `SessionStructure` drop glue. -/
structure DecCalleesPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop where
  region : region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
    ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
      (Q ·.st.pqRatchetState))
  remoteIk : RemoteIdentityKeyPlacedOk A H
  dropSs : DropSessionStructureLocal2PlacedOk A H

/-- Chains one relocatable store-kit-parameterized segment into the remainder of the run. -/
theorem decSegVPlaced_chain [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext) hL
  · exact ⟨sf, hst, hout⟩

/-- Variant of `decSegVPlaced_chain` threading `DecFsCtxPlaced` to the next seam. -/
theorem decSegVPlaced_chainFs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h1 : DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s next)
    (h2 : ∀ s', DecFsCtxPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_463 H)
        (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext) hL
  · exact ⟨sf, hst, hout⟩

section ChainVPlaced

variable [LibsignalPlacement] {H : LibsignalHooks}
  {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
  (hC : DecCalleesPlaced C A ctl S H Q)
  (hS : DecSegsVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope)
  (x : DecryptGhost) (R : SepProp) (s0 : State)
  (hAddr : kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val)

include hH hS in
theorem reachVPlaced_resultFinal (s : State)
    (h : ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chain (hS.write hH x R s0 s h) (fun _ hf => hf.elim)

include hH hC hS in
theorem reachVPlaced_errJoin (pt : Bool) (s : State)
    (h : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x pt R s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chain (hS.errTeardown hH hC.dropSs x pt R s0 s h)
    (reachVPlaced_resultFinal hH hS x R s0)

include hH hC hS hAddr in
theorem reachVPlaced_storeCall (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : StoreCallStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chain (hS.store hH hC.dropSs x ans R s0 s hAddr.1 hfs h) (fun s' h' => h'.elim
    (reachVPlaced_resultFinal hH hS x R s0 s') (reachVPlaced_errJoin hH hC hS x R s0 true s'))

include hH hC hS hAddr in
theorem reachVPlaced_trusted (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : TrustedStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans t R s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  cases t with
  | true =>
    exact decSegVPlaced_chainFs hfs (hS.save hH x ans R s0 s hAddr.2 hfs h) (fun s' hfs' h' => h'.elim
      (fun ⟨ans', hsc⟩ => reachVPlaced_storeCall hH hC hS x R s0 hAddr ans' s' hfs' hsc)
      (reachVPlaced_errJoin hH hC hS x R s0 true s'))
  | false =>
    exact decSegVPlaced_chain (hS.untrusted hH x ans R s0 s h)
      (reachVPlaced_errJoin hH hC hS x R s0 true)

include hH hC hS hAddr in
theorem reachVPlaced_keyReady (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : KeyReadyStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s :=
  decSegVPlaced_chainFs hfs (hS.trust hH x ans R s0 s hAddr.2 hfs h) (fun s' hfs' h' => h'.elim
    (fun ⟨ans', t, ht⟩ => reachVPlaced_trusted hH hC hS x R s0 hAddr ans' t s' hfs' ht)
    (reachVPlaced_errJoin hH hC hS x R s0 true s'))

include hH hC hS hAddr in
theorem reachVPlaced_loadPolled (hQ : ScopePq kit st0 Scope Q)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (s : State)
    (hfs : DecFsCtxPlaced kit ikit H s0 s)
    (h : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s := by
  refine decSegVPlaced_chainFs hfs (hS.dispatch hH x ans R s0 s h) ?_
  rintro s' hfs' (hSome | hNone | hFin)
  · refine decSegVPlaced_chainFs hfs' (hS.regionSome hH Q hC.region hQ x ans R s0 s' hSome) ?_
    intro s'' hfs'' hPost
    exact decSegVPlaced_chainFs hfs'' (hS.postSome hH hC.remoteIk x ans R s0 s'' hPost)
      (fun s3 hfs3 h3 => h3.elim
        (reachVPlaced_keyReady hH hC hS x R s0 hAddr ans s3 hfs3)
        (reachVPlaced_errJoin hH hC hS x R s0 false s3))
  · refine decSegVPlaced_chain (hS.regionNone hH x ans R s0 s' hNone) ?_
    intro s'' hPost
    exact decSegVPlaced_chain (hS.postNone hH x ans R s0 s'' hPost)
      (reachVPlaced_errJoin hH hC hS x R s0 false)
  · exact reachVPlaced_resultFinal hH hS x R s0 s' hFin

end ChainVPlaced

/-- Assembles `withStoresDecPlacedSpecV` with entry-file `envOk` preconditions from the twelve
relocatable segments under `KitFsOk`. -/
theorem withStoresDec_placed_ok_of_segsV_fs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hC : DecCalleesPlaced C A ctl S H Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hAddr := withStoresDecPlacedSpecV_pre_addrOk hpre
  have hfs0 : DecFsCtxPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  exact decSegVPlaced_chainFs hfs0 (hS.load hH x R s0 hfs0 hpc hrun hal hpre)
    (fun s hfs ⟨ans, h⟩ => reachVPlaced_loadPolled hH hC hS x R s0 hAddr hQ ans s hfs h)

/-- Assembles `withStoresDecPlacedSpecV` from the twelve relocatable segments when `envOk` is trivial. -/
theorem withStoresDec_placed_ok_of_segsV [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hC : DecCalleesPlaced C A ctl S H Q) (hQ : ScopePq kit st0 Scope Q)
    (hS : DecSegsVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  subroutine_ok_of_withEnvPre (withStoresDec_placed_ok_of_segsV_fs hH hC hQ hS (.inl htriv))
    fun s => htriv s.fs.files

theorem remoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    RemoteIdentityKeyPlacedOk A H := by
  have _ := Getters.instIsLsBlockProg_29 H
  exact StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_463 H)
    (Getters.remote_identity_key_placed_ok A H)

theorem dropSessionStructureLocal2PlacedOk [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    DropSessionStructureLocal2PlacedOk A H := by
  have _ := CryptoVerification.CliRatchet.Placed.instIsLsBlockProg_442 H
  exact StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_463 H)
    (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_placed_ok hDealloc)

/-- Constructs `DecCalleesPlaced` from the record-decrypt region contract on `lsProg_463 H`. -/
theorem decCalleesPlaced_of_region [LibsignalPlacement] {H : LibsignalHooks}
    {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesPlaced C A ctl S H Q :=
  ⟨hRegion, remoteIdentityKeyPlacedOk A H, dropSessionStructureLocal2PlacedOk hDealloc⟩

/-- Constructs `DecCalleesPlaced` from the record-decrypt region contract on `Record.lsProg_463 H`. -/
theorem decCalleesPlaced_of_recordRegion [LibsignalPlacement] {H : LibsignalHooks}
    {Q : List (BitVec 8) → Prop}
    (hDealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hRegion : region_ok (CryptoVerification.Cli.LibsignalTripleRatchet.Record.lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState))) :
    DecCalleesPlaced C A ctl S H Q :=
  decCalleesPlaced_of_region hDealloc (lsProg_463_eq_record_lsProg_463 H ▸ hRegion)

/-- Relocatable store-kit-parameterized `decrypt_signal` correctness with `withEnvPre`. -/
theorem decryptSignalWithStores_placed_ok_of_kit_fs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (fun _ => True)))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_placed_ok_of_segsV_fs hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    (scopePq_true kit st0 Scope) decSegsVPlaced_ok hKitFs

/-- Relocatable store-kit-parameterized `decrypt_signal` correctness when `envOk` is trivial. -/
theorem decryptSignalWithStores_placed_ok_of_kit [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (fun _ => True)))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  withStoresDec_placed_ok_of_segsV hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    (scopePq_true kit st0 Scope) decSegsVPlaced_ok htriv

/-- Specialization of `decryptSignalWithStores_placed_ok_of_kit_fs` to empty post-quantum state. -/
theorem decryptSignalWithStoresEmpty_placed_ok_of_kit_fs [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (·.st.pqRatchetState = [])))
    (hQ : ScopePq kit st0 Scope (· = []))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 H)) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_placed_ok_of_segsV_fs hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    hQ decSegsVPlaced_ok hKitFs

/-- Specialization of `decryptSignalWithStores_placed_ok_of_kit` to empty post-quantum state. -/
theorem decryptSignalWithStoresEmpty_placed_ok_of_kit [LibsignalPlacement] {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hH : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hRegion : region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre
        (·.st.pqRatchetState = [])))
    (hQ : ScopePq kit st0 Scope (· = []))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 H) wsEntryPCPlaced
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  withStoresDec_placed_ok_of_segsV hH
    (decCalleesPlaced_of_region hH.hooks.dealloc hRegion)
    hQ decSegsVPlaced_ok htriv


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
