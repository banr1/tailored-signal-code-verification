/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Slot Theorems for `decrypt_prekey`

Composes `CliDpPollOkStatePlacedStmt` with `cliDecryptPrekey_ok_state_placed` and
`decPk_slot_ok_state_placed` on block `520`, and transfers the resulting `decPkSlotSpec` contract
to arbitrary caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
open CryptoVerification.CliHandshake.Placed
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

/-- Derives the relocatable `decrypt_prekey` slot contract on block `520` from
`CliDpPollOkStatePlacedStmt`. -/
theorem cliDecryptPrekey_slot_of_poll_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (dpWrapProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpWrapEntryPlaced
      (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  exact decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll mmpl g W X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64)

/-- Transfers `cliDecryptPrekey_slot_of_poll_placed` to any caller block `i < 619`. -/
theorem cliDecryptPrekey_slot_of_poll_placed_at_block [LibsignalPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  exact decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll mmpl g W X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

/-- Packages `cliDecryptPrekey_slot_of_poll_placed_at_block` at `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk_of_poll_placed [LibsignalPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedStmt)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced E2E.HooksE.A0 S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_of_poll_placed_at_block mmpl g W hi X B S Scope hh hRead hDeser hinjK hsub hS hok
      hpoll stk (hneed ▸ h1) h2

/-- `[LibsignalFullPlacement]` counterpart of `cliDecryptPrekey_slot_of_poll_placed`. -/
theorem cliDecryptPrekey_slot_of_poll_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStateFrozenPlacedStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (dpWrapProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpWrapEntryPlaced
      (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) := by
  exact decPk_slot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll mmpl g W X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64)

/-- Transfers `cliDecryptPrekey_slot_of_poll_full_placed` to any caller block `i < 619`. -/
theorem cliDecryptPrekey_slot_of_poll_full_placed_at_block [LibsignalFullPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStateFrozenPlacedStmt)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) := by
  exact decPk_slot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll mmpl g W X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

/-- Packages `cliDecryptPrekey_slot_of_poll_full_placed_at_block` at `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk_of_poll_full_placed [LibsignalFullPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStateFrozenPlacedStmt)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_of_poll_full_placed_at_block mmpl g W hi X B S Scope hh hRead hDeser hinjK hsub
      hS hok hpoll stk (hneed ▸ h1) h2

end CryptoVerification.SignalSession.Cli.RunProofs
