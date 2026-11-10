/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsVX
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Parametric-Panic `MessageDecrypt` Specification (`withStoresDecPlacedSpecVX`)

Generalizes `withStoresDecPlacedSpecV` and `DecSegVPlaced` on `lsProg_463` by replacing the
`x.recvPanics S answers` panic disjunct with an arbitrary predicate `Extra x answers`.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `withStoresDecPlacedSpecV` with `x.recvPanics S answers` replaced by `Extra x answers`. -/
def withStoresDecPlacedSpecVX [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop) : Spec DecryptGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s.sp (wsStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S parse answers).1 ≠ .error .panic ∧
            (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
            kit.callsRel st0 answers (x.model C S parse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
            sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2⌝ ∗
          kit.storeAt (s0.readReg64 .x3)
            (kit.storeFinal st0 answers (x.model C S parse answers).2) ∗
          ikit.identityAt (s0.readReg64 .x5)
            (ikit.idFinal ist0 answers (x.model C S parse answers).2) ∗
          apiDecResultAt A x.ret (x.model C S parse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws C answers) ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
           (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S parse answers).1 = .error .panic ∨ Extra x answers))⌝ ∗
        anyHeap }

theorem withStoresDecPlacedSpecV_eq_VX [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope =
      withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope
        (fun x a => x.recvPanics S a) := rfl

/-- Relocatable segment step relation `DecSegVPlaced` over `withStoresDecPlacedSpecVX … Extra`. -/
def DecSegVXPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (lsProg_463 H).CodeLoaded s.mem →
  ∃ s', Steps (lsProg_463 H) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra)
        x R s0 s')

theorem DecSegVPlaced_eq_VX [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State) (Out : State → Prop) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out =
      DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
        (fun x a => x.recvPanics S a) x R s0 s Out := rfl

theorem decSegVXPlaced_chain [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra) x R s0 s') :
    reaches_outcome (lsProg_463 H)
      (withStoresDecPlacedSpecVX C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext) hL
  · exact ⟨sf, hst, hout⟩


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
