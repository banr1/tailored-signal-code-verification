/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqDecrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmDecrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignal
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `signal_session_ratchet::decrypt_signal` Slot Contract (Placed)

Budget-pool counterparts of the `[LibsignalPlacement]` and `[LibsignalFullPlacement]` slot
contracts for `signal_session_ratchet::decrypt_signal` (Block `463`) under allocation envelope
`CliDecryptSignalSlotEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord messageDecryptSignal)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles IdentityVtablesPlacedOk SessionOnlyVtablesPlacedOk
)
open CryptoVerification.LibsignalPublicApiRepr (serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost coinsOf serviceIdParse uuidTryParse
)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (RunNeeds RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptSignalNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Agree (
  RatchetScopeCoversPq RatchetScopeCoversSm decSigDef decSigKey
  pqDecryptSignalAgrees_decSigDef_aux smDecryptSignalAgrees_decSigDef_aux
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (decDefAux decKeyAux)
open CryptoVerification.SignalSession.Cli.RunRefine (
  PqDecryptSignalAgrees SmDecryptSignalAgrees
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  DistinctSid EncodeInjOn FilesOkPeer scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs decSigSlotSpecPlaced slotsOfPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget (
  w2_inner_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  InnerDecryptPlacedOk decIdKitPlaced decSessKitPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget (
  CliDecryptSignalSlotEnv cliDecryptSignal_slot_of_inner_placed_pe
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

theorem decSigDef_eq_decDefAux (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    decSigDef P Scope = decDefAux P Scope := by
  have hFinal : ∀ F calls,
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal F calls =
        CryptoVerification.SignalSession.Cli.RunProofs.cliFinal F calls := by
    intro F calls
    unfold CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal
      CryptoVerification.SignalSession.Cli.RunProofs.cliFinal
    have hStep :
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliStep F =
          CryptoVerification.SignalSession.Cli.RunProofs.cliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hKey : ∀ F peer me msg coins,
      decSigKey P Scope F peer me msg coins =
        decKeyAux P Scope F peer me msg coins :=
    fun _ _ _ _ _ => rfl
  have hAns : ∀ F peer k,
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer k =
        CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers Scope F peer k := by
    intro F peer k
    unfold CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers
      CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers
    cases k <;> rfl
  funext F peer me msg coins
  unfold decSigDef decDefAux
  rw [hKey F peer me msg coins, hAns F peer]
  generalize messageDecryptSignal P.C (pqxdhSpqrModel P).spqr
    (serializeAddrVals (serviceIdParse uuidTryParse))
    (CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers Scope F peer
      (decKeyAux P Scope F peer me msg coins))
    msg peer me (coinsOf coins) = rc
  rcases rc with ⟨err | pt, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

theorem decSigDef_eq_runProofs (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    decSigDef P Scope = CryptoVerification.SignalSession.Cli.RunProofs.decSigDef P Scope :=
  decSigDef_eq_decDefAux P Scope

/-- Budget-threaded `decSigSlotSpecPlaced` contract for `signal_session_ratchet::decrypt_signal`
(`lsmpl.base 463`) on any caller block `i < 619` under `CliDecryptSignalSlotEnv`. -/
theorem cliDecryptSignal_slot_placed_pe [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptPlacedOk P A lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecPlaced A lim
        (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk) :=
  let hS' := hS.trans (decSigDef_eq_decDefAux P Scope)
  cliDecryptSignal_slot_of_inner_placed_pe P A lim B S Scope tdEnv kitEnv ikitEnv
    (hh.fs callerProg i) hinjK hsub
    (fun F peer me msg coins =>
      congrFun (congrFun (congrFun (congrFun (congrFun hS' F) peer) me) msg) coins)
    hok hvt hivt (w2_inner_placed_at_block P A lim H B tdEnv kitEnv ikitEnv hInner463 hi)
    stk hstk hstk64

theorem cliDecryptSignal_slot_placed [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv) S stk) :=
  cliDecryptSignal_slot_placed_pe ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B S Scope tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok stk hstk hstk64 hi

theorem cliDecryptSignal_slotOk_placed_pe [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptPlacedOk P A lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOfPlaced A lim envs S needs).decryptSignal.OkPlaced
      (lsProg_579 H) (lsmpl.base 463) := by
  intro stk h1 h2
  dsimp only [slotsOfPlaced, mkSlot] at h1 ⊢
  rw [henv]
  exact cliDecryptSignal_slot_placed_pe (i := 579) P A lim H B S Scope tdEnv kitEnv ikitEnv
    hh hvt hivt hInner463 hinjK hsub hS hok stk (hneed ▸ h1) h2

theorem cliDecryptSignal_slotOk_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 : InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOfPlaced A lim envs S needs).decryptSignal.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
  cliDecryptSignal_slotOk_placed_pe ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B S Scope envs needs tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok henv hneed

theorem pqDecryptSignalAgrees_decSigDef_placed (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    PqDecryptSignalAgrees S W :=
  pqDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

theorem smDecryptSignalAgrees_decSigDef_placed (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    SmDecryptSignalAgrees S W.C :=
  smDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

def slotsOfSigFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : RunSlotEnvs)
    (S : RunSem) (needs : RunNeeds) :
    CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots :=
  { slotsOfPlaced A lim envs S needs with
    decryptSignal := mkSlot
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.decSigSlotSpecFrozenPlaced
        A lim envs.decryptSignal S) needs.decryptSignal }

/-- Closed `[LibsignalFullPlacement]` budget-threaded `decSigSlotSpecFrozenPlaced` contract for
`signal_session_ratchet::decrypt_signal` (`lsmpl.base 463`) on any caller block `i < 619`. -/
theorem cliDecryptSignal_slot_full_placed_pe [CryptoVerification.LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
        P A lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.decSigSlotSpecFrozenPlaced
        A lim (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk) :=
  let hS' := hS.trans (decSigDef_eq_decDefAux P Scope)
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.cliDecryptSignal_slot_of_inner_frozen_placed_pe
    P A lim B S Scope tdEnv kitEnv ikitEnv
    (hh.fs callerProg i) hinjK hsub
    (fun F peer me msg coins =>
      congrFun (congrFun (congrFun (congrFun (congrFun hS' F) peer) me) msg) coins)
    hok hvt hivt
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget.w2_inner_full_placed_at_block
      P A lim H B tdEnv kitEnv ikitEnv hInner463 hi)
    stk hstk hstk64

theorem cliDecryptSignal_slot_full_placed [CryptoVerification.LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
        ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (stk : Nat) (hstk : cliDecryptSignalNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 463)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.decSigSlotSpecFrozenPlaced
        A lim (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv) S stk) :=
  cliDecryptSignal_slot_full_placed_pe ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B S Scope tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok stk hstk hstk64 hi

theorem cliDecryptSignal_slotOk_full_placed_pe [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim H)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
        P A lim H B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef P Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOfSigFrozenPlaced A lim envs S needs).decryptSignal.OkPlaced
      (lsProg_579 H) (lsmpl.base 463) := by
  intro stk h1 h2
  dsimp only [slotsOfSigFrozenPlaced, slotsOfPlaced, mkSlot] at h1 ⊢
  rw [henv]
  exact cliDecryptSignal_slot_full_placed_pe (i := 579) P A lim H B S Scope tdEnv kitEnv ikitEnv
    hh hvt hivt hInner463 hinjK hsub hS hok stk (hneed ▸ h1) h2

/-- Instantiates `(slotsOfSigFrozenPlaced ...).decryptSignal.OkPlaced` on Block `579` (`lsProg_579`) under `[LibsignalFullPlacement]`. -/
theorem cliDecryptSignal_slotOk_full_placed [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (envs : RunSlotEnvs) (needs : RunNeeds)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner463 :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
        ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (henv : envs.decryptSignal = CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv)
    (hneed : needs.decryptSignal = cliDecryptSignalNeed B) :
    (slotsOfSigFrozenPlaced A lim envs S needs).decryptSignal.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
  cliDecryptSignal_slotOk_full_placed_pe ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B S Scope envs needs tdEnv kitEnv ikitEnv hh hvt hivt hInner463 hinjK hsub hS hok henv hneed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
