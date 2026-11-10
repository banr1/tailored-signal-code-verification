/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Inner Store-Kit Specification for `decrypt_signal`

`[LibsignalPlacement]` counterparts of `withStoresDecSpecVTP`, `InnerDecryptPlacedOk`, and their
`withLsFrozen`-guarded variants on Block `463` (`signal_session_ratchet::decrypt_signal`).
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
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

noncomputable abbrev cliAnswers := EncryptLemmas.w1CliAnswers
abbrev cliStep := EncryptLemmas.w1CliStep
abbrev cliFinal := EncryptLemmas.w1CliFinal

abbrev decNeedAux_placed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

noncomputable def decKeyAux_placed (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
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

noncomputable def decDefAux_placed (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  match LibsignalSessionApi.messageDecryptSignal W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F peer (decKeyAux_placed W Scope F peer me msg coins)) msg peer me
      (LibsignalTripleRatchetRepr.coinsOf coins) with
  | (.ok pt, calls) => some (some (cliFinal F calls, pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none

theorem decDefAux_eq_model_placed (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.DecryptGhost) :
    decDefAux_placed W Scope F x.rem.val x.loc.val x.msg x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (decKeyAux_placed W Scope F x.rem.val x.loc.val x.msg x.rest)) with
      | (.ok pt, calls) => some (some (cliFinal F calls, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none :=
  rfl

/-- Relocatable tight store-kit contract for `decrypt_signal` threading `tokenInitPlacedAt` and `Slots.DistinctSid`. -/
def withStoresDecPlacedSpecVTP [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  let base := CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX
    C A ctl parse S encRecord kit ikit st0 ist0 Scope (fun _ _ => False)
  { base with
    pre := fun x s =>
      ⌜Slots.DistinctSid parse x.loc.name.bytes x.rem.name.bytes⌝ ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ base.pre x s
    post := fun x s0 sf =>
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ base.post x s0 sf }

noncomputable abbrev decSessKitPlaced [LibsignalPlacement] (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    SessionStoreSpec E2E.HooksE.A0 0#64 :=
  EncryptLemmas.w1SessKitPlaced B F0 peer

noncomputable abbrev decIdKitPlaced [LibsignalPlacement] (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    IdentityStoreSpec E2E.HooksE.A0 0#64 :=
  EncryptLemmas.w1IdKitPlaced B F0 peer

/-- Relocatable inner store-kit hypothesis on Block `463` (`lsProg_463`) at `decSessKitPlaced` and `decIdKitPlaced`. -/
def InnerDecryptPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
    let kit := decSessKitPlaced F0 peer B
    let ikit := decIdKitPlaced F0 peer B
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

def withStoresDecFrozenPlacedSpecVTP [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  withLsFrozen lsmpl (withStoresDecPlacedSpecVTP C A ctl parse S encRecord kit ikit st0 ist0 Scope)

/-- `withLsFrozen`-guarded variant of `InnerDecryptPlacedOk` on Block `463`. -/
def InnerDecryptFrozenPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
    let kit := decSessKitPlaced F0 peer B
    let ikit := decIdKitPlaced F0 peer B
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecFrozenPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
