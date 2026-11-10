/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlot
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn

/-!
# Poll Closure Contract Statements for `decrypt_prekey`

Defines `CliDpPollOkStateStmt` and its extern-parameterized counterpart `CliDpPollOkStateExtStmt`
for the `message_decrypt_prekey` poll closure, along with the specialization bridge at
`cliHookExterns W`.
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

/-- States that the `decrypt_prekey` poll closure `cliDpPollName` satisfies `dpPollSpecState`
at `dpSlotPollKState E2E.HooksE.A0 img B S` under `cliExterns W` for all stack budgets
`dpPollNeed B ≤ stk' ≤ 2 ^ 63`. -/
def CliDpPollOkStateStmt : Prop :=
  ∀ {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
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
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKState E2E.HooksE.A0 img B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
        ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDpPollName)
        ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img)

/-- Extern-parameterized counterpart of `CliDpPollOkStateStmt` over arbitrary `(P, A, ext)`
satisfying `CliExternsOk P A ext` and `RunHooksExt img A (cliExternsWith ext)`. -/
def CliDpPollOkStateExtStmt : Prop :=
  ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDef X P Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ P Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKState A img B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliDpPollName)
        ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img)

/-- Specializes `CliDpPollOkStateExtStmt` to `CliDpPollOkStateStmt` at `cliHookExterns W`. -/
theorem cliDpPollOkStateStmt_of_ext
    (hExt : CliDpPollOkStateExtStmt)
    (hOkW : ∀ W : CliHooks, CliExternsOk ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W)) :
    CliDpPollOkStateStmt :=
  fun W X B S Scope himg hh hRead hDeser hinjK hsub hS hok stk' h1 h2 =>
    hExt ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) X B S Scope
      (hOkW W) himg hh.toExt hRead hDeser hinjK hsub hS hok stk' h1 h2

theorem dpSlotPollKState_need (A : RustAlloc) (img : Obj.Image) (B : RunBudgets) (S : RunSem) :
    (dpSlotPollKState A img B S).need = dpPollNeed B := rfl

example (img : Obj.Image) (B : RunBudgets) (S : RunSem) :
    (dpSlotPollKState E2E.HooksE.A0 img B S).need = dpPollNeed B := rfl
example (img : Obj.Image) (B : RunBudgets) (S : RunSem) :
    dpSlotPollKState E2E.HooksE.A0 img B S = K₀_state img B S := rfl
example (B : RunBudgets) : dpWrapFrame + dpPollNeed B = cliDecryptPrekeyNeed B := by
  simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed]; omega

end CryptoVerification.SignalSession.Cli.RunProofs

