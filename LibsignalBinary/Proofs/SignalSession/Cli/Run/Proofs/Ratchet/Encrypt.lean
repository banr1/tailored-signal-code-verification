/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInner
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqEncrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmEncrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInst

/-!
# `signal_session_ratchet::encrypt` Slot Specification and Model Agreement

Defines the CLI store-answer evaluation (`cliAnswers`, `cliStep`, `cliFinal`) and functional model
`encDef` (with identity lookup key `encKey`) for `signal_session_ratchet::encrypt`, proves the
`encSlotSpec` binary contract, and establishes agreement with the PQXDH and Signal-Message send
transitions.

`encDef` evaluates `LibsignalSessionApi.messageEncrypt` at `UNIX_EPOCH` against `cliAnswers`,
mapping model panics (including `EncryptGhost.sendPanics`) to `none`, `.ok m` to acceptance with
`cliFinal`, and other errors to rejection. Session records at the start of a run lie in
`Scope ⊆ Slots.scopeIn`, while the session store kit operates on `Slots.scopeKit` (which is closed
under a single SPQR step from `scopeIn`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-! ## CLI store answers and final state -/

/-- CLI store answers on `F` for `peer` and queried identity key `k`: loads via
`Slots.loadRec Scope F peer`, evaluates `IdGhost.trusted` and `saveAns` on the freshly opened
identity store, and returns `.ok ()` on `store_session`. -/
noncomputable def cliAnswers (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) (k : Option IdentityKey) : StoreAnswers (List (BitVec 8)) Unit where
  loadSession := Slots.loadRec Scope F peer
  isTrustedIdentity := match k with
    | some k => StoresGhost.opened.identity.trusted cliIo.rd F peer k
    | none => .ok false
  saveIdentity := match k with
    | some k => StoresGhost.opened.identity.saveAns cliIo.rd F peer k
    | none => .ok .newOrUnchanged
  storeSession := .ok ()

/-- Single-call transition on `StoresGhost`: `save_identity` pins the key and `store_session`
writes the serialized record, while loads and trust queries leave stores unchanged. -/
def cliStep (F : FsFiles) (g : StoresGhost) : StoreCall AddrVal (List (BitVec 8)) → StoresGhost
  | .saveIdentity rem k => { g with identity := g.identity.saveUpd cliIo.rd F rem k }
  | .storeSession rem r =>
    { g with sessions := g.sessions.put (Cli.addressText rem) (E2E.Record.encodeRecord r) }
  | _ => g

/-- Final `StoresGhost` obtained by replaying `calls` from `StoresGhost.opened`. -/
def cliFinal (F : FsFiles) (calls : List (StoreCall AddrVal (List (BitVec 8)))) : StoresGhost :=
  calls.foldl (cliStep F) StoresGhost.opened

/-! ## Functional model of `encrypt` -/

/-- Remote identity key queried via `is_trusted_identity` during `message_encrypt`: the remote
identity of `from_session_state` on the loaded current session (`none` if missing). -/
noncomputable def encKey (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) : Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match r.currentSession with
    | some s =>
      match execOk OutgoingTripleRatchet.fromSessionState s.state with
      | .ok (_, taken) => taken.remoteIdentity
      | .error _ => none
    | none => none
  | _ => none

/-- Functional model of `encrypt` at the V1 SPQR model of `W`, CLI address serializer,
`UNIX_EPOCH`, and `cliAnswers`: maps panics to `none`, `.ok m` to acceptance with `cliFinal`, and
other errors to rejection. -/
noncomputable def encDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (ptext coins : List (BitVec 8)) :
    SlotAns CiphertextMessage :=
  match LibsignalSessionApi.messageEncrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) (cliAnswers Scope F peer (encKey Scope F peer))
      ptext peer me unixEpoch coins with
  | (.ok m, calls) => some (some (cliFinal F calls, m))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- Identifies `encDef` on an `EncryptGhost` input at `now = unixEpoch` with `EncryptGhost.model`
evaluated at `cliAnswers`. -/
theorem encDef_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.EncryptGhost)
    (hnow : x.now = unixEpoch) :
    encDef W Scope F x.rem.val x.loc.val x.ptext x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (encKey Scope F x.rem.val)) with
      | (.ok m, calls) => some (some (cliFinal F calls, m))
      | (.error .panic, _) => none
      | (.error _, _) => some none := by
  simp only [encDef, CryptoVerification.LibsignalPublicApi.EncryptGhost.model, hnow]

/-! ## Binary `encSlotSpec` contract -/

/-- Stack budget `2^20 + B.readFile` for `signal_session_ratchet::encrypt`. -/
abbrev cliEncryptNeed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

/-- Binary contract for `signal_session_ratchet::encrypt`: under `cliExterns W`, `readFileSpec`,
`FilesOkPeer Scope`, `encOk₀ Scope`, and `EncodeInjOn scopeKit`, the subroutine satisfies
`encSlotSpec` for any stack budget `cliEncryptNeed B ≤ stk ≤ 2^63`. -/
theorem cliEncrypt_slot {img : Obj.Image} (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : cliEncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
      (encSlotSpec E2E.HooksE.A0 img S stk) := by
  have hFinal : ∀ F calls, cliFinal F calls = EncryptLemmas.w1CliFinal F calls := by
    intro F calls
    unfold cliFinal EncryptLemmas.w1CliFinal
    have hStep : cliStep F = EncryptLemmas.w1CliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      cliAnswers Scope F peer (encKey Scope F peer) =
        EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer) := by
    intro F peer
    have hKey : encKey Scope F peer = EncryptLemmas.w1EncKey Scope F peer := by
      unfold encKey EncryptLemmas.w1EncKey
      rcases Slots.loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold cliAnswers EncryptLemmas.w1CliAnswers
    rcases EncryptLemmas.w1EncKey Scope F peer with _ | _ <;> rfl
  have hDef : encDef ⟨W.C, W.Q⟩ Scope = EncryptLemmas.w1EncDef ⟨W.C, W.Q⟩ Scope := by
    funext F peer me ptext coins
    unfold encDef EncryptLemmas.w1EncDef
    rw [hAns F peer]
    generalize LibsignalSessionApi.messageEncrypt W.C protoSignalCodec
      (pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
      (EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer))
      ptext peer me unixEpoch coins = rc
    rcases rc with ⟨err | m, calls⟩
    · cases err <;> rfl
    · simp only [hFinal F calls]
  exact EncryptLemmas.cliEncrypt_slot W B S Scope himg hh hRead hinjK hsub (hS.trans hDef)
    hok stk hstk hstk64

theorem cliEncrypt_slotOk {img : Obj.Image} (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hneed : needs.encrypt = cliEncryptNeed B) :
    (slotsOf E2E.HooksE.A0 img S needs).encrypt.Ok img (cliExterns W) wrapEncryptName :=
  fun stk h1 h2 =>
    cliEncrypt_slot W B S Scope himg hh hRead hinjK hsub hS hok stk (hneed ▸ h1) h2

/-! ## Agreement with PQXDH and Signal-Message `send` models -/

/-- Every PQXDH domain session record lies in `Scope`. -/
def RatchetScopeCoversPq (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (st : PqParty) x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
    Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)

/-- Every reachable Signal-Message session record lies in `Scope`. -/
def RatchetScopeCoversSm (C : Crypto) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ g : GhostState (List (BitVec 8)), Reach (spqrOffSessionParams C) g →
    Scope (E2E.Record.toRecord E2E.Record.extrasM g)

/-- `PqEncryptAgrees` for `S.encrypt = encDef W Scope`. -/
theorem pqEncryptAgrees_encDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqEncryptAgrees S W := by
  exact Agree.pqEncryptAgrees_encDef_aux S W Scope hS hinj hcov

/-- `SmEncryptAgrees` for `S.encrypt = encDef W Scope`. -/
theorem smEncryptAgrees_encDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmEncryptAgrees S W.C := by
  exact Agree.smEncryptAgrees_encDef_aux S W Scope hS hinj hcov

/-! ## Allocator- and extern-parametric generalization -/

private theorem w1_traceFsSound_cliExternsWith {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound
      (tripleRatchetProgAtExt b (cliExternsWith ext)) :=
  RunGlue.traceFsSound_of_fsTHooks
    (RunGlue.fsTHooks_withPanics (RunGlue.fsTHooks_withCliPanics hOk.fsTraced))
    RunGlue.fsTHooks_none

private theorem encDef_eq_w1EncDef (P : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    encDef P Scope = EncryptLemmas.w1EncDef P Scope := by
  have hFinal : ∀ F calls, cliFinal F calls = EncryptLemmas.w1CliFinal F calls := by
    intro F calls
    unfold cliFinal EncryptLemmas.w1CliFinal
    have hStep : cliStep F = EncryptLemmas.w1CliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      cliAnswers Scope F peer (encKey Scope F peer) =
        EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer) := by
    intro F peer
    have hKey : encKey Scope F peer = EncryptLemmas.w1EncKey Scope F peer := by
      unfold encKey EncryptLemmas.w1EncKey
      rcases Slots.loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold cliAnswers EncryptLemmas.w1CliAnswers
    rcases EncryptLemmas.w1EncKey Scope F peer with _ | _ <;> rfl
  funext F peer me ptext coins
  unfold encDef EncryptLemmas.w1EncDef
  rw [hAns F peer]
  generalize LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer))
    ptext peer me unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · simp only [hFinal F calls]

theorem cliEncrypt_slot_of_inner_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapEncryptName)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withEnvPre
          (EncryptLemmas.withStoresEncSpecVT_cli
            (EncryptLemmas.w1SessKitExt A B img F peer) StoresGhost.opened.sessions
            (EncryptLemmas.w1IdKitExt A B img F peer) StoresGhost.opened.identity
            Slots.scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord)
          (fun s => (EncryptLemmas.w1SessKitExt A B img F peer).envOk s.fs.files ∧
            (EncryptLemmas.w1IdKitExt A B img F peer).envOk s.fs.files)))
    (stk : Nat) (hstk : cliEncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapEncryptName)
      (encSlotSpec A img S stk) :=
  EncryptLemmas.cliEncrypt_slot_of_inner_ext P A (cliExternsWith ext) B S Scope himg
    (w1_traceFsSound_cliExternsWith hOk img.base) hinjK hsub
    (hS.trans (encDef_eq_w1EncDef P Scope)) hok hInner stk hstk hstk64

theorem cliEncrypt_slotOk_of_inner_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapEncryptName)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withEnvPre
          (EncryptLemmas.withStoresEncSpecVT_cli
            (EncryptLemmas.w1SessKitExt A B img F peer) StoresGhost.opened.sessions
            (EncryptLemmas.w1IdKitExt A B img F peer) StoresGhost.opened.identity
            Slots.scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord)
          (fun s => (EncryptLemmas.w1SessKitExt A B img F peer).envOk s.fs.files ∧
            (EncryptLemmas.w1IdKitExt A B img F peer).envOk s.fs.files)))
    (hneed : needs.encrypt = cliEncryptNeed B) :
    (slotsOf A img S needs).encrypt.Ok img (cliExternsWith ext) wrapEncryptName :=
  fun stk h1 h2 =>
    cliEncrypt_slot_of_inner_ext P A ext hOk B S Scope himg hinjK hsub hS hok hInner stk
      (hneed ▸ h1) h2

theorem cliEncrypt_slot_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hVT : EncryptLemmas.WithStoresOkVTExtStmt img P A (cliExternsWith ext))
    (hSessKit : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE
        (EncryptLemmas.w1SessKitExt A B img F peer) Slots.scopeKit E2E.Record.encodeRecord
        (cliExternsWith ext))
    (hIdKit : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE
        img (EncryptLemmas.w1IdKitExt A B img F peer) (cliExternsWith ext))
    (stk : Nat) (hstk : cliEncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapEncryptName)
      (encSlotSpec A img S stk) :=
  EncryptLemmas.cliEncrypt_slot_of_vt_ext P A (cliExternsWith ext) B S Scope himg
    (w1_traceFsSound_cliExternsWith hOk img.base) hinjK hsub
    (hS.trans (encDef_eq_w1EncDef P Scope)) hok hVT hSessKit hIdKit stk hstk hstk64

/-- Instantiates `(slotsOf A img S needs).encrypt.Ok` on `cliExternsWith ext` from
`CliExternsOk P A ext`, `WithStoresOkVTExtStmt`, and the session and identity store-kit contracts. -/
theorem cliEncrypt_slotOk_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hVT : EncryptLemmas.WithStoresOkVTExtStmt img P A (cliExternsWith ext))
    (hSessKit : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE
        (EncryptLemmas.w1SessKitExt A B img F peer) Slots.scopeKit E2E.Record.encodeRecord
        (cliExternsWith ext))
    (hIdKit : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE
        img (EncryptLemmas.w1IdKitExt A B img F peer) (cliExternsWith ext))
    (hneed : needs.encrypt = cliEncryptNeed B) :
    (slotsOf A img S needs).encrypt.Ok img (cliExternsWith ext) wrapEncryptName :=
  fun stk h1 h2 =>
    cliEncrypt_slot_ext P A ext hOk B S Scope himg hinjK hsub hS hok hVT hSessKit hIdKit stk
      (hneed ▸ h1) h2

theorem cliEncrypt_slot_of_ext_witness {img : Obj.Image} (W : CliHooks) (B : RunBudgets)
    (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : cliEncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
      (encSlotSpec E2E.HooksE.A0 img S stk) := by
  have hInnerExt : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith (cliHookExterns W)))
        ((tripleRatchetProgAtExt img.base (cliExternsWith (cliHookExterns W))).fnAddr wrapEncryptName)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withEnvPre
          (EncryptLemmas.withStoresEncSpecVT_cli
            (EncryptLemmas.w1SessKitExt E2E.HooksE.A0 B img F peer) StoresGhost.opened.sessions
            (EncryptLemmas.w1IdKitExt E2E.HooksE.A0 B img F peer) StoresGhost.opened.identity
            Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
          (fun s => (EncryptLemmas.w1SessKitExt E2E.HooksE.A0 B img F peer).envOk s.fs.files ∧
            (EncryptLemmas.w1IdKitExt E2E.HooksE.A0 B img F peer).envOk s.fs.files)) := by
    intro F peer hokF
    rw [← cliExterns_eq W]
    exact EncryptLemmas.w1_inner_ok W B Scope himg hinjK hsub F peer hokF
  have h := cliEncrypt_slot_of_inner_ext ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W)
    (cliExterns_ok W) B S Scope himg hinjK hsub hS hok hInnerExt stk hstk hstk64
  rwa [← cliExterns_eq W] at h

end CryptoVerification.SignalSession.Cli.RunProofs
