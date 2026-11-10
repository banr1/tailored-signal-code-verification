/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVX
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Encrypt
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Defs

/-!
# Inner Store-Kit Specification for `decrypt_signal`

Defines the tight `TokenInit` and `Slots.DistinctSid` store-kit specification
`withStoresDecSpecVTP`, the concrete CLI session and identity store kits `decSessKit` and
`decIdKit`, and the `InnerDecryptOk` interface for `signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev decNeedAux (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

noncomputable def decKeyAux (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match LibsignalSessionApi.SessionRecord.tryDecryptFromRecord W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse) peer me) msg
        (LibsignalTripleRatchetRepr.coinsOf coins) r with
    | .ok (_, r') => r'.currentSession.bind (·.state.remoteIdentity)
    | .error _ => none
  | _ => none

noncomputable def decDefAux (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  match LibsignalSessionApi.messageDecryptSignal W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F peer (decKeyAux W Scope F peer me msg coins)) msg peer me
      (LibsignalTripleRatchetRepr.coinsOf coins) with
  | (.ok pt, calls) => some (some (cliFinal F calls, pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none

theorem decDefAux_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.DecryptGhost) :
    decDefAux W Scope F x.rem.val x.loc.val x.msg x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (decKeyAux W Scope F x.rem.val x.loc.val x.msg x.rest)) with
      | (.ok pt, calls) => some (some (cliFinal F calls, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none :=
  rfl

/-- Tight store-kit contract for `decrypt_signal` threading `TokenInit img` and
`Slots.DistinctSid`, with `Extra := fun _ _ => False` so panics occur only on model panic or
allocation failure. -/
def withStoresDecSpecVTP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  let base := CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
    C A ctl parse S encRecord img kit ikit st0 ist0 Scope (fun _ _ => False)
  { base with
    pre := fun x s =>
      ⌜Slots.DistinctSid parse x.loc.name.bytes x.rem.name.bytes⌝ ∗
        TokenInit img ∗ base.pre x s
    post := fun x s0 sf =>
      TokenInit img ∗ base.post x s0 sf }

abbrev decSessKit (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    SessionStoreSpec E2E.HooksE.A0 img.base :=
  cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

abbrev decIdKit (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    IdentityStoreSpec E2E.HooksE.A0 img.base :=
  cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

/-- Inner store-kit contract for `decrypt_signal` specialized to `decSessKit`, `decIdKit`,
`StoresGhost.opened`, and `Slots.scopeKit` under `FilesOkPeer Slots.scopeIn`. -/
def InnerDecryptOk (img : Obj.Image) (W : CliHooks) (B : RunBudgets) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
    let kit := decSessKit img F0 peer B
    let ikit := decIdKit img F0 peer B
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre
        (withStoresDecSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord img kit ikit
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

/-! ## Allocator- and extern-parametric generalization -/

abbrev decSessKitExt (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost)
    (B : RunBudgets) : SessionStoreSpec A img.base :=
  cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

abbrev decIdKitExt (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost)
    (B : RunBudgets) : IdentityStoreSpec A img.base :=
  cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

theorem decSessKitExt_A0_eq (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    decSessKitExt E2E.HooksE.A0 img F0 peer B = decSessKit img F0 peer B := rfl

theorem decIdKitExt_A0_eq (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    decIdKitExt E2E.HooksE.A0 img F0 peer B = decIdKit img F0 peer B := rfl

/-- Generalization of `InnerDecryptOk` over `P : E2E.PEParams`, `A : RustAlloc`, and extern table `ext'`. -/
def InnerDecryptOkExt (img : Obj.Image) (P : E2E.PEParams) (A : RustAlloc)
    (ext' : String → Option (State → State)) (B : RunBudgets) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
    let kit := decSessKitExt A img F0 peer B
    let ikit := decIdKitExt A img F0 peer B
    subroutine_ok (tripleRatchetProgAtExt img.base ext')
      (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img)
      (withEnvPre
        (withStoresDecSpecVTP P.C A 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel P) E2E.Record.encodeRecord img kit ikit
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

abbrev InnerDecryptOkCliExt (img : Obj.Image) (P : E2E.PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets) : Prop :=
  InnerDecryptOkExt img P A (cliExternsWith ext) B

theorem innerDecryptOkExt_cli_eq (img : Obj.Image) (W : CliHooks) (B : RunBudgets) :
    InnerDecryptOkExt img ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliExterns W) B = InnerDecryptOk img W B := rfl

theorem innerDecryptOkCliExt_witness_eq (img : Obj.Image) (W : CliHooks) (B : RunBudgets) :
    InnerDecryptOkCliExt img ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) B =
      InnerDecryptOk img W B := rfl

theorem decNeedAux_extHookStack_eq :
    decNeedAux ⟨extHookStack⟩ = 2 ^ 20 + 16384 := rfl

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
