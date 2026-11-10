/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Slot Theorems for `decrypt_prekey`

Establishes pointwise (`CliDpPollOkStatePlacedAt`) and quantified (`CliDpPollOkStatePlacedStmt`)
budget-threaded `decPkSlotSpec` contracts on block `520` under `RustCliAllocBudget M`, and transfers
them to caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunNeeds RunSem dpPollNeed mkSlot)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOk₀ cliDecryptPrekeyNeed decPkDef dpWrapFrame)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
  (dpPollProgPlaced dpWrapEntryPlaced dpWrapProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
  (CliDpPollOkStatePlacedAt CliDpPollOkStatePlacedStmt K₀_statePlaced RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
  (cliDecryptPrekey_ok_state_placed cliDecryptPrekey_ok_state_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (decPkSlotSpecPlaced dpSlotPollKStatePlaced dpSlot_ok_state_placed slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

theorem dpSlotPollKStatePlaced_inv_vm [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem)
    (g : DecPkGhost) (st : M.σ) (s0 s1 : State)
    (hfs : s1.fs = s0.fs) (_htr : s1.trace = s0.trace) (hvm : VmPreserved s0 s1) :
    (dpSlotPollKStatePlaced A lim DecPkEnv B S).inv g st s0 ⊢
      (dpSlotPollKStatePlaced A lim DecPkEnv B S).inv g st s1 := by
  dsimp only [dpSlotPollKStatePlaced, slotFramePlaced]
  rw [hfs, A.pool_transport lim st s0 s1 hvm]
  exact Entails.refl _

theorem dpSlotPollKStatePlaced_res_vm [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem)
    (g : DecPkGhost) (st : M.σ) (s0 s1 sm sf : State) (ws : List (BitVec 64))
    (hfs01 : s1.fs = s0.fs) (htr01 : s1.trace = s0.trace) (_hvm01 : VmPreserved s0 s1)
    (hfs_mf : sf.fs = sm.fs) (htr_mf : sf.trace = sm.trace) (hvm_mf : VmPreserved sm sf) :
    (dpSlotPollKStatePlaced A lim DecPkEnv B S).res g st s1 sm ws ⊢
      (dpSlotPollKStatePlaced A lim DecPkEnv B S).res g st s0 sf ws := by
  dsimp only [dpSlotPollKStatePlaced]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs
    (Entails.sepExists_elim fun g' => Entails.sepExists_right g'
      (Entails.sepExists_elim fun e => Entails.sepExists_right e ?_))
  rw [hfs01, htr01, hfs_mf, htr_mf, A.pool_transport lim (M.stepEvents evs st) sm sf hvm_mf]
  exact Entails.refl _

/-- Derives the budget-threaded `decrypt_prekey` slot contract on block `520` from `CliDpPollOkStatePlacedAt`. -/
theorem cliDecryptPrekey_slot_of_pollAt_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn
      CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧
        DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X B S Scope)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (dpWrapProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpWrapEntryPlaced
      (decPkSlotSpecPlaced A lim DecPkEnv S stk) :=
  dpSlot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed (ext := cliGhostExterns g (cliExternsPlaced mmpl W))
      (K₀_statePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' h1 h2 => hpoll hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64)

/-- Derives the budget-threaded `decrypt_prekey` slot contract on block `520` from `CliDpPollOkStatePlacedStmt`. -/
theorem cliDecryptPrekey_slot_of_poll_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn
      CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧
        DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedStmt A lim ReadEnv DeserEnv DecPkEnv)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (dpWrapProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpWrapEntryPlaced
      (decPkSlotSpecPlaced A lim (DecPkEnv W X B Scope) S stk) :=
  cliDecryptPrekey_slot_of_pollAt_placed A lim ReadEnv DeserEnv (DecPkEnv W X B Scope) mmpl g W X B S Scope
    hh hRead hDeser hinjK hsub hS hok (hpoll mmpl g W X B S Scope) stk hstk hstk64

/-- Transfers `cliDecryptPrekey_slot_of_pollAt_placed` to any caller block `i < 619`. -/
theorem cliDecryptPrekey_slot_of_pollAt_placed_at_block [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn
      CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧
        DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X B S Scope)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced A lim DecPkEnv S stk) :=
  dpSlot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := cliGhostExterns g (cliExternsPlaced mmpl W))
      (K₀_statePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' h1 h2 => hpoll hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

/-- Transfers `cliDecryptPrekey_slot_of_poll_placed` to any caller block `i < 619`. -/
theorem cliDecryptPrekey_slot_of_poll_placed_at_block [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn
      CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧
        DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedStmt A lim ReadEnv DeserEnv DecPkEnv)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520)
      (decPkSlotSpecPlaced A lim (DecPkEnv W X B Scope) S stk) :=
  cliDecryptPrekey_slot_of_pollAt_placed_at_block A lim ReadEnv DeserEnv (DecPkEnv W X B Scope)
    mmpl g W hi X B S Scope hh hRead hDeser hinjK hsub hS hok (hpoll mmpl g W X B S Scope) stk hstk hstk64

/-- Packages `cliDecryptPrekey_slot_of_pollAt_placed_at_block` at `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk_of_pollAt_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn
      CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧
        DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X B S Scope)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_of_pollAt_placed_at_block A lim ReadEnv DeserEnv DecPkEnv mmpl g W hi X B S Scope
      hh hRead hDeser hinjK hsub hS hok hpoll stk (hneed ▸ h1) h2

/-- Packages `cliDecryptPrekey_slot_of_poll_placed_at_block` at `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk_of_poll_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    [IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn
      CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧
        DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkStatePlacedStmt A lim ReadEnv DeserEnv DecPkEnv)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim (DecPkEnv W X B Scope) S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_of_pollAt_placed A lim ReadEnv DeserEnv (DecPkEnv W X B Scope) mmpl g W hi X B S
    Scope needs hh hRead hDeser hinjK hsub hS hok (hpoll mmpl g W X B S Scope) hneed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
