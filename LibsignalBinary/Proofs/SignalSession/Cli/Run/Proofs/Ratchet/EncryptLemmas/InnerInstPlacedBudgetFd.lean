/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Guarded Inner Contract Transfer for `encrypt` (Placed)

Precondition-guarded `FdsGe3Closed` counterparts of `W1InnerPlacedOkH`, cross-block transfer from
Block `464`, and `cliEncrypt_slot_placed_pe_fd`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudgetFd

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.EncPlaced (instIsLsBlockProg_464 lsProg_464)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles TraceFsSound ls_subroutine_ok_rocl_of_block
  subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre withLsRoCl
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks StoresGhost cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncDef w1EncryptNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
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
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (encSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget (
  withStoresEncPlacedSpecVT_cli_rocl
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced withStoresEncPlacedSpecVT_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudgetFd (
  cliEncrypt_slot_of_inner_placed_fd cliEncrypt_slot_of_inner_placed_pe_fd
)

/-- `FdsGe3Closed`-guarded Block-`464` inner `withStoresEncPlacedSpecVT_cli` contract over `P : PEParams` and `H : LibsignalHooks`. -/
def W1InnerPlacedOkHFd [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer)) : Prop :=
  ∀ (F : FsFiles) (peer : AddrGhost),
    FilesOkPeer Scope F peer.val →
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok (lsProg_464 H) (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv F peer) StoresGhost.opened.sessions
          ikit (ikitEnv F peer) StoresGhost.opened.identity
          scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs))

abbrev W1InnerPlacedOkFd [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer)) : Prop :=
  W1InnerPlacedOkHFd ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B Scope sendEnv kitEnv ikitEnv

/-- Transfers `W1InnerPlacedOkHFd` from Block `464` (`lsProg_464 H`) to any caller block `i < 619`. -/
theorem w1_inner_placed_at_block_pe_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [hcaller : IsLsBlockProg callerProg i H]
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hInner464 : W1InnerPlacedOkHFd P A lim H B Scope sendEnv kitEnv ikitEnv)
    (hi : i < 619 := by decide)
    (F : FsFiles) (peer : AddrGhost) (hok : FilesOkPeer Scope F peer.val) :
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok callerProg (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv F peer) StoresGhost.opened.sessions
          ikit (ikitEnv F peer) StoresGhost.opened.identity
          scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs)) := by
  intro kit ikit
  have hsub := hInner464 F peer hok
  have hwrap := subroutine_ok_withLsCodeRoLoaded_of_plain (pl := lsmpl) hsub
  have htr := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_464 H)
    i 464 H hcaller (instIsLsBlockProg_464 H)
    (lsmpl.base 464) _ hwrap _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono htr (fun xs R s0 hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · have hrocl := withStoresEncPlacedSpecVT_cli_rocl hpre
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hrocl, hpre⟩
  · dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

theorem w1_inner_placed_at_block_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hInner464 : W1InnerPlacedOkFd mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv)
    (hi : i < 619 := by decide)
    (F : FsFiles) (peer : AddrGhost) (hok : FilesOkPeer Scope F peer.val) :
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok callerProg (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv F peer) StoresGhost.opened.sessions
          ikit (ikitEnv F peer) StoresGhost.opened.identity
          scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs)) :=
  w1_inner_placed_at_block_pe_fd ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B Scope sendEnv kitEnv ikitEnv hInner464 hi F peer hok

/-- Establishes `FdsGe3Closed`-guarded budget-threaded `encSlotSpecPlaced` on any caller block `i < 619`. -/
theorem cliEncrypt_slot_placed_pe_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hfs : TraceFsSound callerProg)
    (hInner464 : W1InnerPlacedOkHFd P A lim H B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = w1EncDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withPreGuard (fun s0 => FdsGe3Closed s0.fs)
        (encSlotSpecPlaced A lim (CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv) S stk)) :=
  cliEncrypt_slot_of_inner_placed_pe_fd P A lim B S Scope sendEnv kitEnv ikitEnv hfs hinjK hsub hS hok
    (w1_inner_placed_at_block_pe_fd P A lim H B Scope sendEnv kitEnv ikitEnv hInner464 hi)
    stk hstk hstk64

theorem cliEncrypt_slot_placed_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hfs : TraceFsSound callerProg)
    (hInner464 : W1InnerPlacedOkFd mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withPreGuard (fun s0 => FdsGe3Closed s0.fs)
        (encSlotSpecPlaced A lim (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv kitEnv ikitEnv) S stk)) :=
  cliEncrypt_slot_of_inner_placed_fd W A lim B S Scope sendEnv kitEnv ikitEnv hfs hinjK hsub hS hok
    (w1_inner_placed_at_block_fd mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv hInner464 hi)
    stk hstk hstk64

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudgetFd
