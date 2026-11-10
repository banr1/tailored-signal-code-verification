/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj

/-!
# Relocatable `[LibsignalPlacement]` D2(c) Wrapper-to-Slot Lift

Relocatable `[LibsignalPlacement]` lift of `CliDpPollOkD2cStatePlacedStmt` through Block `520`
(`dpWrapProgPlaced`) and onto caller blocks `i < 619` (including Block `579`) to discharge
`OverDecPkD2cSlotOkPlaced` and its `LibsignalFrozen` counterpart.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
open CryptoVerification.CliHandshake.Placed
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)

private theorem withPanics_cliGhostExterns_wrapper (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)) =
      cliGhostExterns g (cliExternsPlaced mmpl W) :=
  CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl g W

/-- Placed D2(c) Poll Closure Statement (`[LibsignalPlacement]`): exact D2(c) counterpart to
`CliDpPollOkStatePlacedStmt`, replacing `decPkDef` and
`DecPkOk₀` with `decPkDefD2c` and `DecPkOkD2c`. -/
def CliDpPollOkD2cStatePlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpPollEntryPlaced
        (StoreKit.withLsCodeRoLoaded lsmpl
          (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk'))

/-- `DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))`
(`lsProg_518 (Rust.withPanics...)`) coincides with
`Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))` (`lsProg_518...`) because
`cliGhostExterns g (cliExternsPlaced mmpl W)` is already closed under `Rust.withPanics`. -/
theorem dpPollProgPlaced_eq_poll [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) :
    dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)) =
      Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  dsimp only [dpPollProgPlaced, Poll.dpPollProgPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1ProgPlaced]
  rw [withPanics_cliGhostExterns_wrapper mmpl g W]

/-- Equivalence between `RunProofs.CliDpPollOkD2cStatePlacedStmt` and
`Poll.CliDpPollOkD2cStatePlacedStmt`. -/
theorem cliDpPollOkD2cState_iff_poll_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    CliDpPollOkD2cStatePlacedStmt mmpl g W ↔ Poll.CliDpPollOkD2cStatePlacedStmt mmpl g W := by
  constructor
  · intro h X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2
    have hEq := dpPollProgPlaced_eq_poll mmpl g W
    exact hEq ▸ h X B S Scope hh (hEq.symm ▸ hRead) (hEq.symm ▸ hDeser)
      hinjK hsub hS hok stk' h1 h2
  · intro h X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2
    have hEq := dpPollProgPlaced_eq_poll mmpl g W
    exact hEq.symm ▸ h X B S Scope hh (hEq ▸ hRead) (hEq ▸ hDeser)
      hinjK hsub hS hok stk' h1 h2

/-- Placed D2(c) wrapper-to-slot lift from `CliDpPollOkD2cStatePlacedStmt`: mirrors
`cliDecryptPrekey_slot_of_poll_placed` via `cliDecryptPrekey_ok_state_placed` and
`decPk_slot_ok_state_placed` on Block `520`. -/
theorem cliDecryptPrekey_slot_d2c_of_poll_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStatePlacedStmt mmpl g W)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (dpWrapProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpWrapEntryPlaced
      (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  exact decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64)

/-- Caller-block transfer of `cliDecryptPrekey_slot_d2c_of_poll_placed` onto any block
`i < 619` (e.g. Block `579` `lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))`) at target `lsmpl.base 520`. -/
theorem cliDecryptPrekey_slot_d2c_of_poll_placed_at_block [LibsignalPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStatePlacedStmt mmpl g W)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
    rw [withPanics_cliGhostExterns_wrapper mmpl g W]
    exact hcaller
  exact decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

/-- `RunCalleesPlaced.decryptPrekey` D2(c) slot theorem on any caller block `i < 619` at any
`needs` with `needs.decryptPrekey = cliDecryptPrekeyNeed B`. -/
theorem cliDecryptPrekey_slotOk_d2c_of_poll_placed [LibsignalPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStatePlacedStmt mmpl g W)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced E2E.HooksE.A0 S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_d2c_of_poll_placed_at_block mmpl g W hi X B S Scope hh hRead hDeser hinjK hsub
      hS hok hpoll stk (hneed ▸ h1) h2

/-- Placed caller-side D2(c) `decrypt_prekey` wrapper slot bundle on Block `579`
(`lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))`, matching `SlotPlaced.cliDecryptPrekey_slotOk_of_poll_placed`
via `mkSlot (decPkSlotSpecPlaced E2E.HooksE.A0 S) needs.decryptPrekey`). -/
def OverDecPkD2cSlotOkPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed →
    (mkSlot (decPkSlotSpecPlaced E2E.HooksE.A0 S) needs.decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520)

/-- Discharges `OverDecPkD2cSlotOkPlaced` from `CliDpPollOkD2cStatePlacedStmt` and the A0
ghost-hook / read-file / Stage-2 contracts on `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem decPkD2cSlotOk_of_poll_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hpoll : CliDpPollOkD2cStatePlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkPlaced mmpl g W := by
  intro X S needs hfiles hdec hdecOk hneed
  have hEq := dpPollProgPlaced_eq_poll mmpl g W
  have hRead' : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile) :=
    hEq.symm ▸ hRead
  have hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) :=
    hEq.symm ▸ Slots.sessDeserialize_of_sub_scopeKit_placed_at_block
      (callerProg := Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518)
      (H := cliGhostExterns g (cliExternsPlaced mmpl W)) (Scope := Slots.scopeKit)
      hStage2 (fun _ h => h)
  exact cliDecryptPrekey_slotOk_d2c_of_poll_placed
    (prog := lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 579) mmpl g W (by decide)
    X cliRunBudgets_placed S Slots.scopeIn needs
    hh hRead' hDeser
    Slots.encodeInjOn_deserializeScopeP_Q
    (fun _ h => h) hdec
    (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
    hpoll hneed

/-- Discharges `OverDecPkD2cSlotOkPlaced` from `Poll.CliDpPollOkD2cStatePlacedStmt`. -/
theorem decPkD2cSlotOk_of_pollPoll_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hpoll : Poll.CliDpPollOkD2cStatePlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkPlaced mmpl g W :=
  decPkD2cSlotOk_of_poll_placed mmpl g W hh hRead hStage2
    ((cliDpPollOkD2cState_iff_poll_placed mmpl g W).mpr hpoll)

/-- Discharges `OverDecPkD2cSlotOkPlaced` from `ClosureBaseStagesCliPlacedStmt` and
`D2cStagesPlacedStmt`. -/
theorem decPkD2cSlotOk_of_cliStages_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hSt2 : Poll.ClosureBaseStagesCliPlacedStmt mmpl g W)
    (hD2c : Poll.D2cStagesPlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkPlaced mmpl g W :=
  decPkD2cSlotOk_of_pollPoll_placed mmpl g W hh hRead hStage2
    (Poll.cliDpPollOk_d2c_placed_of_cliStages mmpl g W hSt2 hD2c)

/-- Discharges `OverDecPkD2cSlotOkPlaced` from `ClosureBaseStagesPlacedStmt` and
`D2cStagesPlacedStmt`. -/
theorem decPkD2cSlotOk_of_stages_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hSt2 : Poll.ClosureBaseStagesPlacedStmt mmpl g W)
    (hD2c : Poll.D2cStagesPlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkPlaced mmpl g W :=
  decPkD2cSlotOk_of_pollPoll_placed mmpl g W hh hRead hStage2
    (Poll.cliDpPollOk_d2c_placed_of_stages mmpl g W hSt2 hD2c)

/-! ## `LibsignalFrozen`-Guarded D2(c) Wrapper-to-Slot Lift under `[LibsignalFullPlacement]` -/

def CliDpPollOkD2cStateFrozenPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpPollEntryPlaced
        (withLsFrozen lsmpl
          (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk'))

theorem cliDpPollOkD2cState_iff_poll_frozen_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W ↔ Poll.CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W := by
  constructor
  · intro h X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2
    have hEq := dpPollProgPlaced_eq_poll mmpl g W
    exact hEq ▸ h X B S Scope hh (hEq.symm ▸ hRead) (hEq.symm ▸ hDeser)
      hinjK hsub hS hok stk' h1 h2
  · intro h X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2
    have hEq := dpPollProgPlaced_eq_poll mmpl g W
    exact hEq.symm ▸ h X B S Scope hh (hEq ▸ hRead) (hEq ▸ hDeser)
      hinjK hsub hS hok stk' h1 h2

theorem cliDecryptPrekey_slot_d2c_of_poll_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (dpWrapProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpWrapEntryPlaced
      (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) := by
  exact decPk_slot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64)

theorem cliDecryptPrekey_slot_d2c_of_poll_full_placed_at_block [LibsignalFullPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) := by
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
    rw [withPanics_cliGhostExterns_wrapper mmpl g W]
    exact hcaller
  exact decPk_slot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll X B S Scope hh hRead hDeser hinjK hsub hS hok stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

theorem cliDecryptPrekey_slotOk_d2c_of_poll_full_placed [LibsignalFullPlacement]
    {prog : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_d2c_of_poll_full_placed_at_block mmpl g W hi X B S Scope hh hRead hDeser hinjK hsub
      hS hok hpoll stk (hneed ▸ h1) h2

def OverDecPkD2cSlotOkFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed →
    (mkSlot (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S) needs.decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520)

theorem decPkD2cSlotOk_of_poll_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hpoll : CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl g W := by
  intro X S needs hfiles hdec hdecOk hneed
  have hEq := dpPollProgPlaced_eq_poll mmpl g W
  have hRead' : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile) :=
    hEq.symm ▸ hRead
  have hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) :=
    hEq.symm ▸ Slots.sessDeserialize_of_sub_scopeKit_placed_at_block
      (callerProg := Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518)
      (H := cliGhostExterns g (cliExternsPlaced mmpl W)) (Scope := Slots.scopeKit)
      hStage2 (fun _ h => h)
  exact cliDecryptPrekey_slotOk_d2c_of_poll_full_placed
    (prog := lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 579) mmpl g W (by decide)
    X cliRunBudgets_placed S Slots.scopeIn needs
    hh hRead' hDeser
    Slots.encodeInjOn_deserializeScopeP_Q
    (fun _ h => h) hdec
    (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
    hpoll hneed

theorem decPkD2cSlotOk_of_pollPoll_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hpoll : Poll.CliDpPollOkD2cStateFrozenPlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl g W :=
  decPkD2cSlotOk_of_poll_full_placed mmpl g W hh hRead hStage2
    ((cliDpPollOkD2cState_iff_poll_frozen_placed mmpl g W).mpr hpoll)

theorem decPkD2cSlotOk_of_cliStages_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hSt2 : Poll.ClosureBaseStagesCliFrozenPlacedStmt mmpl g W)
    (hD2c : Poll.D2cStagesFrozenPlacedStmt mmpl g W) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl g W :=
  decPkD2cSlotOk_of_pollPoll_full_placed mmpl g W hh hRead hStage2
    (Poll.cliDpPollOk_d2c_frozen_placed_of_cliStages mmpl g W hSt2 hD2c)

end CryptoVerification.SignalSession.Cli.RunProofs
