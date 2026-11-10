/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrusted
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOver
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverInstExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperState
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj

/-!
# D2(c) Wrapper-to-Slot Lift

Lifts the state-coupled `D2(c)` poll closure statement (`CliDpPollOkD2cStateAt` and
`CliDpPollOkD2cStateStmt`) through the outer `decrypt_prekey` wrapper and sret/trace slot adapter
to produce `DecPkD2cSlotOk img` and its `Ext`-parameterized counterpart `DecPkD2cSlotOkExt img`.
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

/-- D2(c) Poll Closure Statement at image `img`: exact D2(c) counterpart to
`CliDpPollOkStateStmt`, replacing `decPkDef` and `DecPkOk₀` with
`decPkDefD2c` and `DecPkOkD2c`. -/
def CliDpPollOkD2cStateAt (img : Obj.Image) : Prop :=
  ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKState E2E.HooksE.A0 img B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
        ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDpPollName)
        ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img)

/-- Image-polymorphic D2(c) Poll Closure Statement (exact binder match to `CliDpPollOkStateStmt`). -/
def CliDpPollOkD2cStateStmt : Prop :=
  ∀ {img : Obj.Image}, CliDpPollOkD2cStateAt img

/-- Caller-side D2(c) `decrypt_prekey` wrapper slot bundle (`DecPkD2cSlotOk img`): specialized to
`decPkDefD2c` and `DecPkOkD2c` at `Slots.scopeIn` and `cliDecryptPrekeyNeed cliRunBudgets`,
unrestricted on `m.inner` (`m.inner.length + 2048 < 2 ^ 32`, covering all versions and non-matching
sessions). -/
def DecPkD2cSlotOk (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    (slotsOf E2E.HooksE.A0 img S needs).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName

/-- D2(c) wrapper-to-slot lift from `CliDpPollOkD2cStateAt img`: mirrors
`Slot.cliDecryptPrekey_slot_of_poll` via `cliDecryptPrekey_ok_state` and `decPk_slot_ok_state`. -/
theorem cliDecryptPrekey_slot_d2c_of_pollAt {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
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
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateAt img)
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

/-- D2(c) wrapper-to-slot lift from `CliDpPollOkD2cStateStmt`. -/
theorem cliDecryptPrekey_slot_d2c_of_poll {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
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
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec E2E.HooksE.A0 img S stk) :=
  cliDecryptPrekey_slot_d2c_of_pollAt W X B S Scope himg hh hRead hDeser hinjK hsub hS hok
    hpoll stk hstk hstk64

/-- `RunCallees.decryptPrekey` D2(c) slot theorem from `CliDpPollOkD2cStateAt img`. -/
theorem cliDecryptPrekey_slotOk_d2c_of_pollAt {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
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
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B)
    (hpoll : CliDpPollOkD2cStateAt img) :
    (slotsOf E2E.HooksE.A0 img S needs).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_d2c_of_pollAt W X B S Scope himg hh hRead hDeser hinjK hsub hS hok
      hpoll stk (hneed ▸ h1) h2

/-- Discharges `DecPkD2cSlotOk img` directly from `Obj.Loads libsignalSessionImage img` and
`CliDpPollOkD2cStateAt img` (instantiating `RunHooks.cli`, `cliReadFile_ok`,
`sessDeserialize_scopeKit_cli`, and `encodeInjOn_deserializeScopeP_Q`). -/
theorem decPkD2cSlotOk_of_pollAt {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpoll : CliDpPollOkD2cStateAt img) :
    DecPkD2cSlotOk img :=
  fun X W S needs hfiles hdec hdecOk hneed =>
    cliDecryptPrekey_slotOk_d2c_of_pollAt W X cliRunBudgets S Slots.scopeIn needs himg
      (RunHooks.cli W img)
      (cliReadFile_ok W img cliRunBudgets.readFile)
      (Slots.sessDeserialize_scopeKit_cli W himg)
      Slots.encodeInjOn_deserializeScopeP_Q
      (fun _ h => h)
      hdec
      (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
      hneed
      hpoll

/-- Discharges `DecPkD2cSlotOk img` from `Obj.Loads libsignalSessionImage img` and
`CliDpPollOkD2cStateStmt`. -/
theorem decPkD2cSlotOk_of_poll {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpoll : CliDpPollOkD2cStateStmt) :
    DecPkD2cSlotOk img :=
  decPkD2cSlotOk_of_pollAt himg hpoll

/-- Unconditional CLI instantiation of `DecPkD2cSlotOk img` from
`Obj.Loads libsignalSessionImage img` via `Poll.cliDpPollOk_d2c_at`. -/
theorem decPkD2cSlotOk_cli {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    DecPkD2cSlotOk img :=
  decPkD2cSlotOk_of_pollAt himg Poll.cliDpPollOk_d2c_at

/-! ## `Ext`-Parameterized D2(c) Wrapper-to-Slot Lift (`CliExternsOk P A ext`) -/

/-- `Ext`-parameterized D2(c) Poll Closure Statement at image `img`: definitionally equal to
`Poll.CliDpPollOkD2cStateAtExt img`. -/
def CliDpPollOkD2cStateAtExt (img : Obj.Image) : Prop :=
  ∀ (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X P Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c P Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKState A img B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliDpPollName)
        ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img)

/-- Image-polymorphic `Ext`-parameterized D2(c) Poll Closure Statement (definitionally equal to
`Poll.CliDpPollOkD2cStateStmtExt`). -/
def CliDpPollOkD2cStateStmtExt : Prop :=
  ∀ {img : Obj.Image}, CliDpPollOkD2cStateAtExt img

/-- Caller-side `Ext` D2(c) `decrypt_prekey` wrapper slot bundle (`DecPkD2cSlotOkExt img`): definitionally equal to `MainHops.DecPkD2cSlotOkExt img`. -/
def DecPkD2cSlotOkExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)), CliExternsOk P A ext →
    ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPkDefD2c X P Slots.scopeIn →
      S.decPkOk = DecPkOkD2c P Slots.scopeIn →
      needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
      (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName

/-- `Ext`-parameterized D2(c) wrapper-to-slot lift from `CliDpPollOkD2cStateAtExt img`: mirrors
`Slot.cliDecryptPrekey_slot_of_poll_ext` via `cliDecryptPrekey_ok_state` and
`decPk_slot_ok_state_ext`. -/
theorem cliDecryptPrekey_slot_d2c_of_pollAt_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : extHookStack ≤ B.readFile)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X P Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c P Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateAtExt img)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec A img S stk) :=
  decPk_slot_ok_state_ext A (cliExternsWith ext) img B S stk hstk hstk64
    (cliDecryptPrekey_ok_state (ext := cliExternsWith ext) (dpSlotPollKState A img B S)
      (fun stk' h1 h2 => hpoll P A ext X B S Scope hOk himg hread hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKState] at hstk ⊢; omega)
      hstk64)

/-- `Ext`-parameterized D2(c) wrapper-to-slot lift from `CliDpPollOkD2cStateStmtExt`. -/
theorem cliDecryptPrekey_slot_d2c_of_poll_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : extHookStack ≤ B.readFile)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X P Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c P Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateStmtExt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec A img S stk) :=
  cliDecryptPrekey_slot_d2c_of_pollAt_ext P A ext X B S Scope hOk himg hread hinjK hsub hS hok
    hpoll stk hstk hstk64

/-- `Ext`-parameterized `RunCallees.decryptPrekey` D2(c) slot theorem from
`CliDpPollOkD2cStateAtExt img`. -/
theorem cliDecryptPrekey_slotOk_d2c_of_pollAt_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (needs : RunNeeds)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : extHookStack ≤ B.readFile)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X P Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c P Scope F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B)
    (hpoll : CliDpPollOkD2cStateAtExt img) :
    (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_d2c_of_pollAt_ext P A ext X B S Scope hOk himg hread hinjK hsub hS hok
      hpoll stk (hneed ▸ h1) h2

/-- Discharges `DecPkD2cSlotOkExt img` directly from `Obj.Loads libsignalSessionImage img` and
`CliDpPollOkD2cStateAtExt img` (discharging `extHookStack ≤ cliRunBudgets.readFile` and
`encodeInjOn_deserializeScopeP_Q` unconditionally for arbitrary `(P, A, ext)`). -/
theorem decPkD2cSlotOk_ext_of_pollAt {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpoll : CliDpPollOkD2cStateAtExt img) :
    DecPkD2cSlotOkExt img :=
  fun X P A ext hOk S needs hfiles hdec hdecOk hneed =>
    cliDecryptPrekey_slotOk_d2c_of_pollAt_ext P A ext X cliRunBudgets S Slots.scopeIn needs
      hOk himg (by decide)
      Slots.encodeInjOn_deserializeScopeP_Q
      (fun _ h => h)
      hdec
      (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
      hneed
      hpoll

/-- Discharges `DecPkD2cSlotOkExt img` from `Obj.Loads libsignalSessionImage img` and
`CliDpPollOkD2cStateStmtExt`. -/
theorem decPkD2cSlotOk_ext_of_poll {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpoll : CliDpPollOkD2cStateStmtExt) :
    DecPkD2cSlotOkExt img :=
  decPkD2cSlotOk_ext_of_pollAt himg hpoll

/-- Discharges `DecPkD2cSlotOkExt img` from `Obj.Loads libsignalSessionImage img` and
`Poll.D2cStagesExtStmt`. -/
theorem decPkD2cSlotOk_ext_of_stages {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hSt : Poll.D2cStagesExtStmt) :
    DecPkD2cSlotOkExt img :=
  decPkD2cSlotOk_ext_of_pollAt himg (Poll.cliDpPollOk_d2c_at_ext_of_stages hSt)

/-- Discharges `DecPkD2cSlotOkExt img` from `Obj.Loads libsignalSessionImage img` and the four
leaf upstream contracts (`hHkdfExt`, `hHkdfExp`, `hInit`, `hTryDec`) via
`Poll.d2cStages_ext_of_leaf_contracts`. -/
theorem decPkD2cSlotOk_ext_of_leaf_contracts {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hHkdfExt : ∀ {img' : Obj.Image} (P : PEParams) (A : RustAlloc)
      (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img' →
      E2E.Pqxdh.Initiator.PqxdhHkdfExtractOk_ext (modelPrims X P) img' (cliExternsWith ext))
    (hHkdfExp : ∀ {img' : Obj.Image} (P : PEParams) (A : RustAlloc)
      (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img' →
      E2E.Pqxdh.Initiator.PqxdhHkdfExpandMultiInfoOk_ext
        (modelPrims X P) img' (cliExternsWith ext))
    (hInit : ∀ {img' : Obj.Image} (P : PEParams) (A : RustAlloc)
      (ext : String → Option (State → State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img' →
      CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
        img' A P.C.F (cliExternsWith ext))
    (hTryDec : ∀ {img' : Obj.Image} (P : PEParams) (A : RustAlloc)
      (ext : String → Option (State → State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img' →
      subroutine_ok (tripleRatchetProgAtExt img'.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img'.base (cliExternsWith ext)).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
          uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img')) :
    DecPkD2cSlotOkExt img :=
  decPkD2cSlotOk_ext_of_stages himg
    (Poll.d2cStages_ext_of_leaf_contracts hHkdfExt hHkdfExp hInit hTryDec)

end CryptoVerification.SignalSession.Cli.RunProofs
