/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperState

/-!
# Slot Theorems for `decrypt_prekey`

Composes the poll closure contract (`CliDpPollOkStateStmt` / `CliDpPollOkStateExtStmt`) with the
wrapper reduction (`cliDecryptPrekey_ok_state`) and slot bridge (`decPk_slot_ok_state`) to establish
`decPkSlotSpec` for `signal_session_handshake::decrypt_prekey`.
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

/-- Derives `decPkSlotSpec` at `E2E.HooksE.A0` and `cliExterns W` from `CliDpPollOkStateStmt` via
`cliDecryptPrekey_ok_state` and `decPk_slot_ok_state`. -/
theorem cliDecryptPrekey_slot_of_poll {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStateStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec E2E.HooksE.A0 img S stk) := by
  exact decPk_slot_ok_state W img B S stk hstk hstk64
    (cliDecryptPrekey_ok_state (ext := cliExterns W) (K₀_state img B S)
      (fun stk' h1 h2 => hpoll W X B S Scope himg hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_state, dpSlotPollKState] at hstk ⊢; omega)
      hstk64)

/-- Main `decrypt_prekey` slot theorem at allocator `E2E.HooksE.A0` and `cliExterns W` for all
stack budgets `cliDecryptPrekeyNeed B ≤ stk ≤ 2 ^ 63`. -/
theorem cliDecryptPrekey_slot {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec E2E.HooksE.A0 img S stk) := by
  exact cliDecryptPrekey_slot_of_poll W X B S Scope himg hh hRead hDeser hinjK hsub hS hok
    (hpoll := Poll.cliDpPollOk_state_of_stages Poll.stages2_inst) stk hstk hstk64

/-- Packages `cliDecryptPrekey_slot` at any `needs` with `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (needs : RunNeeds)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (slotsOf E2E.HooksE.A0 img S needs).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot W X B S Scope himg hh hRead hDeser hinjK hsub hS hok stk (hneed ▸ h1) h2

/-- Extern-parameterized `decrypt_prekey` slot theorem from `CliDpPollOkStateExtStmt` at arbitrary
`(P, A)` and `cliExternsWith ext`. -/
theorem cliDecryptPrekey_slot_of_poll_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ P Scope F peer me pm)
    (hpoll : CliDpPollOkStateExtStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec A img S stk) :=
  decPk_slot_ok_state_ext A (cliExternsWith ext) img B S stk hstk hstk64
    (cliDecryptPrekey_ok_state (ext := cliExternsWith ext) (dpSlotPollKState A img B S)
      (fun stk' h1 h2 =>
        hpoll P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKState] at hstk ⊢; omega)
      hstk64)

/-- Packages `cliDecryptPrekey_slot_of_poll_ext` at any `needs` with `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk_of_poll_ext {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (needs : RunNeeds)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ P Scope F peer me pm)
    (hpoll : CliDpPollOkStateExtStmt)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_of_poll_ext P A ext X B S Scope hOk himg hh hRead hDeser
      hinjK hsub hS hok hpoll stk (hneed ▸ h1) h2

end CryptoVerification.SignalSession.Cli.RunProofs

