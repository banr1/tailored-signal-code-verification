/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Guarded `signal_session_ratchet::encrypt` Slot Contract (Placed)

`FdsGe3Closed`-precondition-guarded counterparts of `cliEncrypt_slot_placed` and
`cliEncrypt_slotOk_placed` for `signal_session_ratchet::encrypt` (Block `464`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudgetFd

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (RunNeeds RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunProofs (cliEncryptNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Agree (encDef)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer encOk₀ scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SpqrSendBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs encSlotSpecPlaced slotsOfPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudgetFd (
  W1InnerPlacedOkFd W1InnerPlacedOkHFd
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget (
  encDef_eq_w1EncDef
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

/-- `FdsGe3Closed`-guarded budget-threaded `encSlotSpecPlaced` contract for
`signal_session_ratchet::encrypt` (`lsmpl.base 464`) on any caller block `i < 619`. -/
theorem cliEncrypt_slot_placed_pe_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hh : RunHooksPlaced A lim H)
    (hInner464 : W1InnerPlacedOkHFd P A lim H B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = encDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : cliEncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withPreGuard (fun s0 => FdsGe3Closed s0.fs)
        (encSlotSpecPlaced A lim (CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv) S stk)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudgetFd.cliEncrypt_slot_placed_pe_fd
    P A lim H B S Scope sendEnv kitEnv ikitEnv
    (hh.fs callerProg i) hInner464 hinjK hsub (hS.trans (encDef_eq_w1EncDef P Scope)) hok
    stk hstk hstk64 hi

theorem cliEncrypt_slot_placed_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hInner464 : W1InnerPlacedOkFd mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : cliEncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withPreGuard (fun s0 => FdsGe3Closed s0.fs)
        (encSlotSpecPlaced A lim
          (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv kitEnv ikitEnv) S stk)) :=
  cliEncrypt_slot_placed_pe_fd ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B S Scope sendEnv kitEnv ikitEnv hh hInner464 hinjK hsub hS hok stk hstk hstk64 hi

theorem cliEncrypt_slotOk_placed_pe_fd [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hh : RunHooksPlaced A lim H)
    (hInner464 : W1InnerPlacedOkHFd P A lim H B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = encDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (henv : envs.encrypt = CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv)
    (hneed : needs.encrypt = cliEncryptNeed B) :
    ({ (slotsOfPlaced A lim envs S needs).encrypt with
       spec := fun stk =>
         withPreGuard (fun s0 => FdsGe3Closed s0.fs)
           ((slotsOfPlaced A lim envs S needs).encrypt.spec stk) }).OkPlaced
      (lsProg_579 H) (lsmpl.base 464) := by
  intro stk h1 h2
  dsimp only [slotsOfPlaced, mkSlot] at h1 ⊢
  rw [henv]
  exact cliEncrypt_slot_placed_pe_fd (i := 579) P A lim H B S Scope sendEnv kitEnv ikitEnv
    hh hInner464 hinjK hsub hS hok stk (hneed ▸ h1) h2

theorem cliEncrypt_slotOk_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hInner464 : W1InnerPlacedOkFd mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = encDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (henv : envs.encrypt = CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv kitEnv ikitEnv)
    (hneed : needs.encrypt = cliEncryptNeed B) :
    ({ (slotsOfPlaced A lim envs S needs).encrypt with
       spec := fun stk =>
         withPreGuard (fun s0 => FdsGe3Closed s0.fs)
           ((slotsOfPlaced A lim envs S needs).encrypt.spec stk) }).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464) :=
  cliEncrypt_slotOk_placed_pe_fd ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B S Scope envs needs sendEnv kitEnv ikitEnv hh hInner464 hinjK hsub hS hok henv hneed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudgetFd
