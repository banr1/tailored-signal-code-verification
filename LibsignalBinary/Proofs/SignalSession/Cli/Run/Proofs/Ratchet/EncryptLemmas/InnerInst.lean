/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInner
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet

/-!
# Inner Store-Kit Contract Instantiation for `encrypt`

Discharges the inner `withStoresEncSpecVT_cli` obligation of `cliEncrypt_slot_of_inner` by
combining `withStores_okVT_fs_cli`, the session and identity store-kit contracts, and the
`scopeIn` / `scopeKit` record invariants to establish `cliEncrypt_slot`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

private theorem specVT_cli_eq {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecVT_cli
      kit st0 ikit ist0 Scope C ctl uuidParse S encRecord =
    withStoresEncSpecVT_cli kit st0 ikit ist0 Scope C ctl uuidParse S encRecord :=
  rfl

private theorem spqrV1_eq_spqrV1W (W : CliHooks) :
    CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K = pqxdhSpqrModel ⟨W.C, W.Q⟩ :=
  rfl

theorem w1_inner_ok {img : Obj.Image} (W : CliHooks) (B : RunBudgets)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (F : FsFiles) (peer : AddrGhost)
    (hok : Slots.FilesOkPeer Scope F peer.val) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
      (withEnvPre
        (withStoresEncSpecVT_cli
          (w1SessKit B img F peer) StoresGhost.opened.sessions
          (w1IdKit B img F peer) StoresGhost.opened.identity Slots.scopeKit
          W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
        (fun s => (w1SessKit B img F peer).envOk s.fs.files ∧
          (w1IdKit B img F peer).envOk s.fs.files)) := by
  have h :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okVT_fs_cli W
      (kit := w1SessKit B img F peer) (st0 := StoresGhost.opened.sessions)
      (ikit := w1IdKit B img F peer) (ist0 := StoresGhost.opened.identity)
      (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord)
      0#64 himg
      (Slots.cliSessKitOkSE_scopeKit_trTrap W (readStk := B.readFile) himg
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Slots.cliIdKitOkIE_trTrap W (readStk := B.readFile) himg
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (cliSessionStoreSpec_vtablesOk himg)
      (cliIdentityStoreSpec_vtablesOk himg)
      (Or.inr ⟨⟨cliSessionStoreSpec_quiet, cliIdentityStoreSpec_quiet⟩,
        Slots.traceFsSound_trTrap W img.base⟩)
      w1_scopeIn
      w1_scopeQ
      (fun {x r sess otr taken k m otr'} haddr h15 =>
        w1_recOk ⟨W.C, W.Q⟩ hinjK hsub hok haddr
          (Eq.mp
            (congrArg
              (fun S =>
                StepsThroughEncrypt
                  ((w1SessKit B img F peer).ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.rem.val)
                  W.C S uuidTryParse x r sess otr taken k m otr')
              (spqrV1_eq_spqrV1W W))
            h15))
  have hspec :
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecVT_cli
        (w1SessKit B img F peer) StoresGhost.opened.sessions
        (w1IdKit B img F peer) StoresGhost.opened.identity Slots.scopeKit
        W.C 0#64 uuidTryParse (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
        E2E.Record.encodeRecord =
      withStoresEncSpecVT_cli
        (w1SessKit B img F peer) StoresGhost.opened.sessions
        (w1IdKit B img F peer) StoresGhost.opened.identity Slots.scopeKit
        W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩)
        E2E.Record.encodeRecord :=
    (specVT_cli_eq (img := img) (w1SessKit B img F peer) StoresGhost.opened.sessions
      (w1IdKit B img F peer) StoresGhost.opened.identity Slots.scopeKit
      W.C 0#64 uuidTryParse (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
      E2E.Record.encodeRecord).trans
      (congrArg
        (fun S =>
          withStoresEncSpecVT_cli
            (w1SessKit B img F peer) StoresGhost.opened.sessions
            (w1IdKit B img F peer) StoresGhost.opened.identity Slots.scopeKit
            W.C 0#64 uuidTryParse S E2E.Record.encodeRecord)
        (spqrV1_eq_spqrV1W W))
  exact Eq.mp
    (congrArg
      (fun sp =>
        subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
          ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
          (withEnvPre sp
            (fun s => (w1SessKit B img F peer).envOk s.fs.files ∧
              (w1IdKit B img F peer).envOk s.fs.files)))
      hspec)
    h

/-- Establishes the `encSlotSpec` contract for `signal_session_ratchet::encrypt`. -/
theorem cliEncrypt_slot {img : Obj.Image} (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (_hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
      (encSlotSpec E2E.HooksE.A0 img S stk) :=
  cliEncrypt_slot_of_inner W B S Scope himg hh hinjK hsub hS hok
    (w1_inner_ok W B Scope himg hinjK hsub) stk hstk hstk64

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
