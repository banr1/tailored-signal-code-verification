/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded `signal_session_ratchet::decrypt_signal` Slot Contract (Placed)

`FdsGe3Closed`-threaded and `withPreFdsGe3Closed` slot contracts for
`signal_session_ratchet::decrypt_signal` (Block `463`) called from Block `579` under
`[LibsignalFullPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalHooks lsmpl)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityVtablesPlacedOk SessionOnlyVtablesPlacedOk)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (RunNeeds RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptSignalNeed decSigDef)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv decSigSlotSpecFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
  (decSigSlotSpecFrozenPlaced_withFds_to_preFd decSigSlotSpecFrozenPlaced_withFds_to_withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (cliDecryptSignal_slot_full_placed_pe slotsOfSigFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed slotWithFdsGe3Closed
   slotWithPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-- Closed `withFdsGe3Closed` slot contract for `signal_session_ratchet::decrypt_signal` on `callerProg` when `lim.enforced = true`. -/
theorem cliDecryptSignal_slot_full_placed_pe_withFds [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (H : LibsignalHooks) [hcaller : IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced (withFds A) lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptFrozenPlacedOk P (withFds A) lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (withFdsGe3Closed
        (decSigSlotSpecFrozenPlaced A lim
          (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk)) :=
  decSigSlotSpecFrozenPlaced_withFds_to_withFds A henf
    (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk
    (cliDecryptSignal_slot_full_placed_pe (i := i) P (withFds A) lim H B S Scope
      tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok stk hstk hstk64 hi)

theorem cliDecryptSignal_slot_full_placed_pe_preFd [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (H : LibsignalHooks) [hcaller : IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced (withFds A) lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptFrozenPlacedOk P (withFds A) lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (withPreFdsGe3Closed
        (decSigSlotSpecFrozenPlaced A lim
          (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk)) :=
  decSigSlotSpecFrozenPlaced_withFds_to_preFd A henf
    (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk
    (cliDecryptSignal_slot_full_placed_pe (i := i) P (withFds A) lim H B S Scope
      tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok stk hstk hstk64 hi)

theorem cliDecryptSignal_slotOk_full_placed_pe_withFds [LibsignalFullPlacement]
    {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced (withFds A) lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptFrozenPlacedOk P (withFds A) lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotWithFdsGe3Closed
      (slotsOfSigFrozenPlaced A lim envs S needs).decryptSignal).OkPlaced
      (lsProg_579 H) (lsmpl.base 463) := by
  intro stk h1 h2
  dsimp only [slotWithFdsGe3Closed, slotsOfSigFrozenPlaced, slotsOfPlaced, mkSlot] at h1 ⊢
  rw [henv]
  exact cliDecryptSignal_slot_full_placed_pe_withFds (i := 579) P A henf H B S Scope
    tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok stk (hneed ▸ h1) h2

theorem cliDecryptSignal_slotOk_full_placed_pe_preFd [LibsignalFullPlacement]
    {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced (withFds A) lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptFrozenPlacedOk P (withFds A) lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigFrozenPlaced A lim envs S needs).decryptSignal).OkPlaced
      (lsProg_579 H) (lsmpl.base 463) :=
  okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed
    (cliDecryptSignal_slotOk_full_placed_pe_withFds P A henf H B S Scope envs needs
      tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok henv hneed)

/-- Closed `slotWithFdsGe3Closed` `OkPlaced` contract for `decrypt_signal` on Block `579` (`lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))`). -/
theorem cliDecryptSignal_slotOk_full_placed_withFds [LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 :
      InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ (withFds A) lim
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotWithFdsGe3Closed
      (slotsOfSigFrozenPlaced A lim envs S needs).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
  cliDecryptSignal_slotOk_full_placed_pe_withFds ⟨W.C, W.Q⟩ A henf
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) B S Scope envs needs
    tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok henv hneed

theorem cliDecryptSignal_slotOk_full_placed_preFd [LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 :
      InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ (withFds A) lim
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigFrozenPlaced A lim envs S needs).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
  cliDecryptSignal_slotOk_full_placed_pe_preFd ⟨W.C, W.Q⟩ A henf
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) B S Scope envs needs
    tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok henv hneed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd
