/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsVX -- shake: keep

/-!
# Parametric-Panic CLI `MessageDecrypt` Specification (`withStoresDecSpecVX`)

Generalizes `withStoresDecSpecV` and `DecSegV` on the CLI image by replacing the `x.recvPanics S answers`
panic disjunct with an arbitrary predicate `Extra x answers`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSessionApi

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

set_option linter.unusedVariables false in
/-- `withStoresDecSpecV` with `x.recvPanics S answers` replaced by `Extra x answers`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop) : Spec DecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s.sp (wsStackV kit ikit) ∗ A.pool
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
          protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C answers) ∗
          logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
           (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S parse answers).1 = .error .panic ∨ Extra x answers))⌝ ∗
        anyHeap }
    img

/-- Segment step relation `DecSegV` specialized to `withStoresDecSpecVX … Extra`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegVX (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
  ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra)
        x R s0 s')

/-- `DecSegVX` specialized to `trTrapProgAt img.base C abs`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegVX_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (trTrapProgAt img.base C abs).CodeLoaded s.mem →
  ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra)
        x R s0 s')

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegVX_of_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (hOut : ∀ s', Out s' → s'.status = .Running)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegVX_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope Extra x R s0 s Out) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegVX img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨s', hsteps, hout⟩ := h ((trTrapProgAt_codeLoaded_iff img.base C ctl abs s.mem).mpr hL)
  rcases hout with hO | hSub
  · exact ⟨s', ProofLib.Variant.Steps.of_trapsOnly (trapsOnly_trTrap_kit img.base C ctl abs) hsteps
      (.of_running (hOut s' hO)), Or.inl hO⟩
  · exact ⟨s', ProofLib.Variant.Steps.of_trapsOnly (trapsOnly_trTrap_kit img.base C ctl abs) hsteps
      (ProofLib.Variant.SubroutineOutcome.outcomeStatus hSub), Or.inr hSub⟩

end CryptoVerification.LibsignalPublicApi.MessageDecrypt
