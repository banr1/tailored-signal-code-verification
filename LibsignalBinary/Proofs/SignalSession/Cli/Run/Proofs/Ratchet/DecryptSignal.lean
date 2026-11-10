/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.Core
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqDecrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmDecrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGlue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Top
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet

/-!
# `signal_session_ratchet::decrypt_signal` Slot Specification and Model Agreement

Defines the functional model `decSigDef` (and remote identity lookup key `decSigKey`) for
`signal_session_ratchet::decrypt_signal`, proves the `decSigSlotSpec` binary contract, and
establishes agreement with the PQXDH and Signal-Message receive transitions.

`decSigDef` evaluates `LibsignalSessionApi.messageDecryptSignal` against the CLI store answers
(`cliAnswers`), committing `cliFinal` on success, mapping panics (including a decrypted session
lacking a remote identity) to `none`, and mapping all other errors to rejection. Because
`decSigSlotSpec`'s `onPanic` clause allows only genuine model panics or allocation failure, the
binary proof uses the tight record-decryption contract rather than the looser `recvPanics`
over-approximation.
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

/-! ## Functional model of `decrypt_signal` -/

/-- Remote identity key queried via `is_trusted_identity` during `message_decrypt_signal`: the
remote identity of the current session returned by `try_decrypt_from_record` (`none` if loading or
decryption fails or if no remote identity is present). -/
noncomputable def decSigKey (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
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

/-- Functional model of `decrypt_signal` at the V1 SPQR model of `W`, CLI address serializer,
`cliAnswers`, and `coinsOf coins`: maps model panics to `none`, `.ok pt` to acceptance with
`cliFinal`, and other errors to rejection. -/
noncomputable def decSigDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  match LibsignalSessionApi.messageDecryptSignal W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F peer (decSigKey W Scope F peer me msg coins)) msg peer me
      (LibsignalTripleRatchetRepr.coinsOf coins) with
  | (.ok pt, calls) => some (some (cliFinal F calls, pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- Identifies `decSigDef` on a `DecryptGhost` input with `DecryptGhost.model` evaluated at `cliAnswers`. -/
theorem decSigDef_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.DecryptGhost) :
    decSigDef W Scope F x.rem.val x.loc.val x.msg x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (decSigKey W Scope F x.rem.val x.loc.val x.msg x.rest)) with
      | (.ok pt, calls) => some (some (cliFinal F calls, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none := by
  rfl

/-! ## Binary `decSigSlotSpec` contract -/

/-- Stack budget `2^20 + B.readFile` for `signal_session_ratchet::decrypt_signal`. -/
abbrev cliDecryptSignalNeed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

/-- Binary contract for `signal_session_ratchet::decrypt_signal`: under `cliExterns W`,
`readFileSpec`, `FilesOkPeer Scope`, `Slots.DistinctSid`, and `EncodeInjOn scopeKit`, the
subroutine satisfies `decSigSlotSpec` for any stack budget `cliDecryptSignalNeed B ≤ stk ≤ 2^63`. -/
theorem cliDecryptSignal_slot {img : Obj.Image} (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapDecryptSignalName)
      (decSigSlotSpec E2E.HooksE.A0 img S stk) := by
  let _ := hRead
  exact DecryptLemmas.cliDecryptSignal_slot_of_inner W B S Scope himg hh hinjK hsub
    (fun F peer me msg coins =>
      congrFun (congrFun (congrFun (congrFun (congrFun hS F) peer) me) msg) coins)
    hok (DecryptLemmas.innerDecryptOk W B himg) stk hstk hstk64

theorem cliDecryptSignal_slotOk {img : Obj.Image} (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOf E2E.HooksE.A0 img S needs).decryptSignal.Ok img (cliExterns W)
      wrapDecryptSignalName :=
  fun stk h1 h2 =>
    cliDecryptSignal_slot W B S Scope himg hh hRead hinjK hsub hS hok stk (hneed ▸ h1) h2

/-! ## Agreement with PQXDH and Signal-Message `recv` models -/

/-- `PqDecryptSignalAgrees` for `S.decryptSignal = decSigDef W Scope`. -/
theorem pqDecryptSignalAgrees_decSigDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqDecryptSignalAgrees S W := by
  exact Agree.pqDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

/-- `SmDecryptSignalAgrees` for `S.decryptSignal = decSigDef W Scope`. -/
theorem smDecryptSignalAgrees_decSigDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmDecryptSignalAgrees S W.C := by
  exact Agree.smDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

/-! ## Allocator- and extern-parametric generalization -/

theorem cliDecryptSignalNeed_extHookStack_eq :
    cliDecryptSignalNeed ⟨extHookStack⟩ = 2 ^ 20 + 16384 := rfl

theorem traceFsSound_of_cliExternsOk {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    TraceFsSound (tripleRatchetProgAtExt b (cliExternsWith ext)) :=
  RunGlue.traceFsSound_of_fsTHooks
    (RunGlue.fsTHooks_withPanics (RunGlue.fsTHooks_withCliPanics hOk.fsTraced))
    RunGlue.fsTHooks_none

theorem cliDecryptSignal_slot_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext' : String → Option (State → State)) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext'))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hInner : DecryptLemmas.InnerDecryptOkExt img P A ext' B)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext')
      ((tripleRatchetProgAtExt img.base ext').fnAddr wrapDecryptSignalName)
      (decSigSlotSpec A img S stk) :=
  DecryptLemmas.cliDecryptSignal_slot_of_inner_ext P A ext' B S Scope himg hFs hinjK hsub
    (fun F peer me msg coins =>
      congrFun (congrFun (congrFun (congrFun (congrFun hS F) peer) me) msg) coins)
    hok hInner stk hstk hstk64

theorem cliDecryptSignal_slot_of_inner_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hInner : DecryptLemmas.InnerDecryptOkCliExt img P A ext B)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapDecryptSignalName)
      (decSigSlotSpec A img S stk) :=
  cliDecryptSignal_slot_ext P A (cliExternsWith ext) B S Scope himg
    (traceFsSound_of_cliExternsOk hOk img.base) hinjK hsub hS hok hInner stk hstk hstk64

theorem cliDecryptSignal_slotOk_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base (cliExternsWith ext)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hInner : DecryptLemmas.InnerDecryptOkCliExt img P A ext B)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOf A img S needs).decryptSignal.Ok img (cliExternsWith ext)
      wrapDecryptSignalName :=
  fun stk h1 h2 =>
    cliDecryptSignal_slot_ext P A (cliExternsWith ext) B S Scope himg hFs hinjK hsub hS hok
      hInner stk (hneed ▸ h1) h2

theorem cliDecryptSignal_slotOk_ext_of_inner {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hInner : DecryptLemmas.InnerDecryptOkCliExt img P A ext B)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOf A img S needs).decryptSignal.Ok img (cliExternsWith ext)
      wrapDecryptSignalName :=
  cliDecryptSignal_slotOk_ext P A ext B S Scope needs himg
    (traceFsSound_of_cliExternsOk hOk img.base) hinjK hsub hS hok hInner hneed

alias cliDecryptSignal_slotOk_of_inner_ext := cliDecryptSignal_slotOk_ext_of_inner
alias cliDecryptSignal_slotOk_of_cliExternsOk := cliDecryptSignal_slotOk_ext_of_inner

theorem cliDecryptSignal_slot_of_callees_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hCallees : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt
      img P.C A 0#64 (pqxdhSpqrModel P) (cliExternsWith ext) (fun _ => True))
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapDecryptSignalName)
      (decSigSlotSpec A img S stk) :=
  cliDecryptSignal_slot_of_inner_ext P A ext hOk B S Scope himg hinjK hsub hS hok
    (DecryptLemmas.innerDecryptOkCliExt_of_callees B hOk himg hCallees hreadStk) stk hstk hstk64

theorem cliDecryptSignal_slotOk_of_callees_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hCallees : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt
      img P.C A 0#64 (pqxdhSpqrModel P) (cliExternsWith ext) (fun _ => True))
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    (slotsOf A img S needs).decryptSignal.Ok img (cliExternsWith ext)
      wrapDecryptSignalName :=
  cliDecryptSignal_slotOk_ext_of_inner P A ext hOk B S Scope needs himg hinjK hsub hS hok
    (DecryptLemmas.innerDecryptOkCliExt_of_callees B hOk himg hCallees hreadStk) hneed

theorem cliDecryptSignal_slotOk_of_region_and_drop_ext {img : Obj.Image} (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (pqxdhSpqrModel P) img).withVRegs)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      img.base A (cliExternsWith ext))
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    (slotsOf A img S needs).decryptSignal.Ok img (cliExternsWith ext)
      wrapDecryptSignalName :=
  cliDecryptSignal_slotOk_ext_of_inner P A ext hOk B S Scope needs himg hinjK hsub hS hok
    (DecryptLemmas.innerDecryptOkCliExt_of_region_and_drop B hOk himg hreg hdrop hreadStk) hneed

theorem cliDecryptSignal_slot_of_region_ext {img : Obj.Image} (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (pqxdhSpqrModel P) img).withVRegs)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapDecryptSignalName)
      (decSigSlotSpec A img S stk) :=
  cliDecryptSignal_slot_of_inner_ext P A ext hOk B S Scope himg hinjK hsub hS hok
    (DecryptLemmas.innerDecryptOkCliExt_of_region B hOk himg hreg hreadStk) stk hstk hstk64

/-- Instantiates `(slotsOf A img S needs).decryptSignal.Ok` on `cliExternsWith ext` from
`CliExternsOk P A ext` and the tight V1 record-decryption region contract. -/
theorem cliDecryptSignal_slotOk_of_region_ext {img : Obj.Image} (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hreg : region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A 0#64 uuidTryParse
        (pqxdhSpqrModel P) img).withVRegs)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B)
    (hreadStk : extHookStack ≤ B.readFile := by decide) :
    (slotsOf A img S needs).decryptSignal.Ok img (cliExternsWith ext)
      wrapDecryptSignalName :=
  cliDecryptSignal_slotOk_ext_of_inner P A ext hOk B S Scope needs himg hinjK hsub hS hok
    (DecryptLemmas.innerDecryptOkCliExt_of_region B hOk himg hreg hreadStk) hneed

theorem DecryptLemmas.innerDecryptOkExt_of_hyps {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext' : String → Option (State → State)) (B : RunBudgets)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext'))
    (hHyps : ∀ (F0 : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsExt
        img P.C A uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord ext'
        (DecryptLemmas.decSessKitExt A img F0 peer B)
        (DecryptLemmas.decIdKitExt A img F0 peer B)
        StoresGhost.opened.sessions Slots.scopeKit)
    (hCallees : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecCalleesTPExt
      img P.C A 0#64 (pqxdhSpqrModel P) ext' (fun _ => True)) :
    DecryptLemmas.InnerDecryptOkExt img P A ext' B := by
  intro F0 peer hok
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDec_okVTP_distinct_fs_ext
    (ist0 := StoresGhost.opened.identity)
    (hHyps F0 peer hok)
    hCallees
    (fun _ _ ses hsc hcur => ⟨Slots.scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
    (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.cliFilesKits_fsOk hFs)

theorem DecryptLemmas.decModelRecOkAt_decSessKitExt {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hok : Slots.FilesOkPeer Slots.scopeIn F0 peer.val) :
    ∀ (x : CryptoVerification.LibsignalPublicApi.DecryptGhost)
      (rec : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8))
      (rec' : SessionRecord (List (BitVec 8))),
      (DecryptLemmas.decSessKitExt A img F0 peer B).addrOk x.rem.val →
      (DecryptLemmas.decSessKitExt A img F0 peer B).ScopeAt Slots.scopeKit
        StoresGhost.opened.sessions x.rem.val rec →
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
        P.C (pqxdhSpqrModel P) uuidTryParse x rec = .ok (pt, rec') →
      (DecryptLemmas.decSessKitExt A img F0 peer B).RecOk rec' :=
  fun x rec pt rec' haddr hsc hdec =>
    Slots.cliDecModelRecOkAt_opened (Scope₀ := Slots.scopeIn) (fun _ h => h) hok
      x rec rec' pt haddr hsc hdec

end CryptoVerification.SignalSession.Cli.RunProofs
