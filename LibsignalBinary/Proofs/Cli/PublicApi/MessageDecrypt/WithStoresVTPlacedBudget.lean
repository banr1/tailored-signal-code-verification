/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Token-Framed CLI `decrypt_signal` (`WithStoresVTPlacedBudget`)

Specializes `WithStoresVT.CorePlacedBudget` (`withStoresDecPlacedSpecVTP` and
`withStoresDecPlacedSpecVT` on `lsProg_463` under `RustCliAllocBudget M`) to `trTrapExternsPlaced H`
and `lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))`, including concrete file-kit,
`RunHooksPlaced`, and `withLsFrozen`-guarded corollaries.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.Variant SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement libsignalSessionLib lsRustDeallocSym ls_fnAddr_block_ultra lsmpl
)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (
  region_ok_restrictPre_true wsEntryPCPlaced
)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT (IdOrDistinctSid)
open CryptoVerification.Cli.LibsignalTripleRatchet (msgDecryptName)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463 lsProg_463)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.RecordX (RecordInScopeP)
open CryptoVerification.LibsignalPublicApi (DecryptGhost RecordInScope)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (ScopePq decryptRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles KitFsOk NoFsEv SessionStoreSpec TraceFsSound withEnvPre
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel noAllocShimSpec region_ok region_ok_of_trapsOnly rngTrap rngTrap_isTrap
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (ReadRule)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks CliGhostHooksFs cliGhostExterns traceFsSound_lsProg_cli_ghost
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error cliGhostExterns_panic_option_expect_failed
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget (
  DecCalleesTFPlaced DecCalleesTPlaced DecCalleesTPFPlaced DecCalleesTPPlaced
  recordDecryptPlacedSpecP recordDecryptPlacedSpecT recordDecryptPlacedSpecTF
  recordDecryptPlacedSpecTPTight recordDecryptPlacedSpecTPTightF
  withStoresDecPlacedSpecVT withStoresDecPlacedSpecVTF
  withStoresDecPlacedSpecVTP withStoresDecPlacedSpecVTPF
  withStoresDec_okVTF_fs_placed withStoresDec_okVTF_placed
  withStoresDec_okVTPF_distinct_fs_placed withStoresDec_okVTPF_fs_placed
  withStoresDec_okVTPF_placed withStoresDec_okVTP_distinct_fs_placed
  withStoresDec_okVTP_fs_placed withStoresDec_okVTP_placed
  withStoresDec_okVT_fs_placed withStoresDec_okVT_placed
  withStoresDec_reachVTPF_fs_placed withStoresDec_reachVTP_fs_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget (
  DecFsCtxExtPlaced DecHypsExtPlaced
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks publicApiDecHooksPlaced_of_hooks
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

export LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget (
  DecFsCtxExtPlaced
  DecHypsExtPlaced
)

alias withStoresDecPlacedSpecVTF :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTF
alias withStoresDecPlacedSpecVT :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVT
alias withStoresDecPlacedSpecVTPF :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTPF
alias withStoresDecPlacedSpecVTP :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP
alias recordDecryptPlacedSpecP :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.recordDecryptPlacedSpecP
alias recordDecryptPlacedSpecTF :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.recordDecryptPlacedSpecTF
alias recordDecryptPlacedSpecT :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.recordDecryptPlacedSpecT
alias recordDecryptPlacedSpecTPTightF :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.recordDecryptPlacedSpecTPTightF
alias recordDecryptPlacedSpecTPTight :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.recordDecryptPlacedSpecTPTight
alias DecCalleesTPFPlaced :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.DecCalleesTPFPlaced
alias DecCalleesTPPlaced :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.DecCalleesTPPlaced
alias DecCalleesTFPlaced :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.DecCalleesTFPlaced
alias DecCalleesTPlaced :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.DecCalleesTPlaced
alias withStoresDec_reachVTPF_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_reachVTPF_fs_placed
alias withStoresDec_reachVTP_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_reachVTP_fs_placed
alias withStoresDec_okVTPF_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTPF_fs_placed
alias withStoresDec_okVTP_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTP_fs_placed
alias withStoresDec_okVTPF_distinct_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTPF_distinct_fs_placed
alias withStoresDec_okVTP_distinct_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTP_distinct_fs_placed
alias withStoresDec_okVTPF_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTPF_placed
alias withStoresDec_okVTP_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTP_placed
alias withStoresDec_okVTF_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTF_fs_placed
alias withStoresDec_okVT_fs_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVT_fs_placed
alias withStoresDec_okVTF_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTF_placed
alias withStoresDec_okVT_placed :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVT_placed

/-! ## Entry-address, `trTrapExternsPlaced`, and `TrapsOnly` transfer helpers -/

theorem wsEntryPCPlaced_eq_base463 [LibsignalPlacement] :
    wsEntryPCPlaced = lsmpl.base 463 := rfl

theorem wsEntryPCPlaced_eq_fnAddr [LibsignalPlacement] :
    wsEntryPCPlaced = libsignalSessionLib.fnAddr lsmpl msgDecryptName :=
  (ls_fnAddr_block_ultra (pl := lsmpl) (i := 463) (by decide)).symm

/-- Placed extern map overriding `"libsignal_session_rng_fill"` with `rngTrap`. -/
abbrev trTrapExternsPlaced (H : LibsignalHooks) : LibsignalHooks :=
  ProofLib.Variant.trapAt (· == "libsignal_session_rng_fill") rngTrap H

private theorem trapsOnly_rebase_trTrapPlaced (pc : Program) (b : BitVec 64) (H : LibsignalHooks) :
    TrapsOnly (pc.rebase b (trTrapExternsPlaced H)) (pc.rebase b H) := by
  refine TrapsOnly.rebase pc b ?_
  intro n
  by_cases hr : n = "libsignal_session_rng_fill"
  · subst hr
    right
    refine ⟨rngTrap, ?_, rngTrap_isTrap⟩
    simp [trTrapExternsPlaced, ProofLib.Variant.trapAt]
  · left
    have hbeq : (n == "libsignal_session_rng_fill") = false := beq_false_of_ne hr
    simp [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq]

private theorem subroutine_ok_of_trTrapPlaced {α : Type} {pc : Program} {b addr : BitVec 64}
    {H : LibsignalHooks} {spec : Spec α}
    (h : subroutine_ok (pc.rebase b (trTrapExternsPlaced H)) addr spec) :
    subroutine_ok (pc.rebase b H) addr spec :=
  subroutine_ok.of_trapsOnly (trapsOnly_rebase_trTrapPlaced pc b H) h

/-- `TrapsOnly` relation from `lsProg_463 (trTrapExternsPlaced ...)` to `lsProg_463 (cliGhostExterns ...)`. -/
theorem trapsOnly_lsProg_463_trTrap_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    TrapsOnly
      (lsProg_463 (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  trapsOnly_rebase_trTrapPlaced blkPC_463 (blkPl_463).base
    (cliGhostExterns gh (cliExternsPlaced mmpl W))

/-- Transfers budget `DecCalleesTPFPlaced` from `trTrapExternsPlaced` to `cliGhostExterns`. -/
theorem decCalleesTPFPlaced_of_trTrap_cli [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} {Q : List (BitVec 8) → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h : DecCalleesTPFPlaced F0 W.C A lim ctl S tdEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) Q) :
    DecCalleesTPFPlaced F0 W.C A lim ctl S tdEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) Q where
  region := region_ok_of_trapsOnly (trapsOnly_lsProg_463_trTrap_cli mmpl gh W) h.region
  remoteIk := subroutine_ok_of_trTrapPlaced h.remoteIk
  dropSs := subroutine_ok_of_trTrapPlaced h.dropSs

/-- Transfers budget `DecCalleesTFPlaced` from `trTrapExternsPlaced` to `cliGhostExterns`. -/
theorem decCalleesTFPlaced_of_trTrap_cli [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} {Q : List (BitVec 8) → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h : DecCalleesTFPlaced F0 W.C A lim ctl S tdEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) Q) :
    DecCalleesTFPlaced F0 W.C A lim ctl S tdEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) Q where
  region := region_ok_of_trapsOnly (trapsOnly_lsProg_463_trTrap_cli mmpl gh W) h.region
  remoteIk := subroutine_ok_of_trTrapPlaced h.remoteIk
  dropSs := subroutine_ok_of_trTrapPlaced h.dropSs

/-! ## Trap-program specializations (`trTrapExternsPlaced H`) -/

/-- Weak-precondition (`RecordInScopeP`) budget hypothesis bundle at `trTrapExternsPlaced H`. -/
abbrev DecHypsPPlaced_trap [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A.repAlloc 0#64) (ssEnv : SessionStoreBudgetEnv ss)
    (id : IdentityStoreSpec A.repAlloc 0#64) (idEnv : IdentityStoreBudgetEnv id)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsExtPlaced C A lim parse S encRecord (trTrapExternsPlaced H) ss ssEnv id idEnv st0 Scope

/-- Tight-panic, weak-precondition budget callee bundle at `trTrapExternsPlaced H`. -/
abbrev DecCalleesTPFPlaced_trap [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPFPlaced F0 C A lim ctl S tdEnv (trTrapExternsPlaced H) Q

abbrev DecCalleesTPPlaced_trap [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPPlaced C A lim ctl S tdEnv (trTrapExternsPlaced H) Q

/-- `F0`-framed `recordDecryptPlacedSpecTF` budget callee bundle at `trTrapExternsPlaced H`. -/
abbrev DecCalleesTFPlaced_trap [LibsignalPlacement] {M : AllocCostModel} (F0 : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTFPlaced F0 C A lim ctl S tdEnv (trTrapExternsPlaced H) Q

abbrev DecCalleesTPlaced_trap [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPlaced C A lim ctl S tdEnv (trTrapExternsPlaced H) Q

/-- Constructs `DecCalleesTPFPlaced_trap` at `Q := fun _ => True` from an unconditional region proof. -/
theorem decCalleesTPFPlaced_trap_of_uncond [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} {H : LibsignalHooks}
    (hDealloc : HookSat (trTrapExternsPlaced H) lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hreg : region_ok (lsProg_463 (trTrapExternsPlaced H)) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTightF F0 C A lim ctl uuidTryParse S tdEnv).withVRegs) :
    DecCalleesTPFPlaced_trap F0 C A lim ctl S tdEnv H (fun _ => True) :=
  DecCalleesTPFPlaced.of_region hDealloc (region_ok_restrictPre_true hreg)

alias DecCalleesTPFPlaced_trap.of_uncond := decCalleesTPFPlaced_trap_of_uncond

theorem withStoresDec_reachVTP_fs_placed_trap [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExtPlaced kit ikit (trTrapExternsPlaced H) s0 s0) :
    reaches_outcome (lsProg_463 (trTrapExternsPlaced H))
      (withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 s0 :=
  withStoresDec_reachVTP_fs_placed hH hC hQ x st_init R s0 hid hpc hrun hpre hal hfs

theorem withStoresDec_okVTP_fs_placed_trap [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (trTrapExternsPlaced H))) :
    subroutine_ok (lsProg_463 (trTrapExternsPlaced H)) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTP_distinct_fs_placed_trap [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (trTrapExternsPlaced H))) :
    subroutine_ok (lsProg_463 (trTrapExternsPlaced H)) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTP_placed_trap [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 (trTrapExternsPlaced H)) wsEntryPCPlaced
      ((withStoresDecPlacedSpecVTP C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
        (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1)) :=
  withStoresDec_okVTP_placed hH hC hQ htriv

theorem withStoresDec_okVT_fs_placed_trap [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTPlaced_trap C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (trTrapExternsPlaced H))) :
    subroutine_ok (lsProg_463 (trTrapExternsPlaced H)) wsEntryPCPlaced
      (withEnvPre
        (withStoresDecPlacedSpecVT C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVT_fs_placed hH hscopeIn hC hQ hKitFs

theorem withStoresDec_okVT_placed_trap [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTPlaced_trap C A lim ctl S tdEnv H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 (trTrapExternsPlaced H)) wsEntryPCPlaced
      (withStoresDecPlacedSpecVT C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope) :=
  withStoresDec_okVT_placed hH hscopeIn hC hQ htriv

/-! ## Placed CLI program (`lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))`) -/

private theorem hookSat_sessionShimBudget_of_withVmPreserved {H : LibsignalHooks}
    {sym : String} (h : HookSat H sym (withVmPreserved noAllocShimSpec)) :
    HookSat H sym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

/-- Constructs budget `DecHypsExtPlaced` from `PublicApiDecHooksPlaced` and the placed budget store-kit bundles. -/
theorem decHypsExtPlaced_of_hooks [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {ss : SessionStoreSpec A.repAlloc 0#64} {ssEnv : SessionStoreBudgetEnv ss}
    {id : IdentityStoreSpec A.repAlloc 0#64} {idEnv : IdentityStoreBudgetEnv id}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hhooks : PublicApiDecHooksPlaced A lim H)
    (hkit : SessionOnlyKitPlacedOkSE A lim ss ssEnv Scope encRecord H)
    (hikit : IdentityStoreKitPlacedOkI A lim id idEnv H)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExtPlaced C A lim parse S encRecord H ss ssEnv id idEnv st0 Scope where
  hooks := hhooks
  kit := hkit
  ikit := hikit
  scopeInP := hscopeInP
  recOk := hrecOk

/-- Constructs budget `DecHypsExtPlaced` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` via `publicApiDecHooksPlaced_of_hooks`. -/
theorem decHypsExtPlaced_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ss : SessionStoreSpec A.repAlloc 0#64} {ssEnv : SessionStoreBudgetEnv ss}
    {id : IdentityStoreSpec A.repAlloc 0#64} {idEnv : IdentityStoreBudgetEnv id}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hkit : SessionOnlyKitPlacedOkSE A lim ss ssEnv Scope encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim id idEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExtPlaced W.C A lim parse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) ss ssEnv id idEnv st0 Scope :=
  decHypsExtPlaced_of_hooks
    (publicApiDecHooksPlaced_of_hooks mmpl gh W hG hStrClone)
    hkit hikit hscopeInP hrecOk

/-- Constructs budget `DecHypsExtPlaced` directly from `RunHooksPlaced`. -/
theorem decHypsExtPlaced_of_runHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ss : SessionStoreSpec A.repAlloc 0#64} {ssEnv : SessionStoreBudgetEnv ss}
    {id : IdentityStoreSpec A.repAlloc 0#64} {idEnv : IdentityStoreBudgetEnv id}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hkit : SessionOnlyKitPlacedOkSE A lim ss ssEnv Scope encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim id idEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExtPlaced W.C A lim parse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) ss ssEnv id idEnv st0 Scope := by
  have hmc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := by
    have h : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memcpy"
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec) :=
      (show CryptoVerification.LibsignalTripleRatchet.lsMemcpySym = "memcpy" by decide) ▸
        hh.codecHooks.memcpy
    rcases h with ⟨f, hf, hsat⟩
    refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
    have hpre' : s0.mem ⊨
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec).pre
          (dst, src, bs) s0 ∗ R := by
      dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
        memcpyRegionSpec] at hpre ⊢
      simpa only [sepConj_assoc] using hpre
    exact hsat (dst, src, bs) R s0 hrun hpre' hsp
  exact decHypsExtPlaced_of_hooks
    ⟨hookSat_sessionShimBudget_of_withVmPreserved hh.codecHooks.shim,
      hh.codecHooks.alloc, hh.codecHooks.dealloc, hmc, hh.stringClone,
      cliGhostExterns_panic_handle_error mmpl gh W,
      cliGhostExterns_panic_option_expect_failed mmpl gh W⟩
    hkit hikit hscopeInP hrecOk

/-- Discharges `KitFsOk` on `lsProg_463` for any pair of `Quiet` store kits. -/
theorem cliQuietKits_placed_fsOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hFs : CliGhostHooksFs gh) {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    (hq : kit.Quiet ∧ ikit.Quiet) :
    KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  KitFsOk.of_sound hq (traceFsSound_lsProg_cli_ghost mmpl gh W hFs)

/-- Discharges `KitFsOk` for vtable-overridden `cliSessionStoreSpec` and `cliIdentityStoreSpec` on any `TraceFsSound` program. -/
theorem cliFilesKits_placed_fsOk {A : RustAlloc} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    {ssVt ssIdVt idVt : BitVec 64} {P : Program}
    (hfs : TraceFsSound P) :
    let kit : SessionStoreSpec A 0#64 :=
      { cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer s1 s2 s3 s4 with
        ss_vt := ssVt, id_vt := ssIdVt }
    let ikit : IdentityStoreSpec A 0#64 :=
      { cliIdentityStoreSpec A 0#64 rd F0 pathOk peer is1 is2 is3 is4 with
        id_vt := idVt }
    KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) P :=
  KitFsOk.of_sound
    ⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
      ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩
    hfs

/-- Discharges `KitFsOk` on `lsProg_463 H` for `Quiet` store kits from `RunHooksPlaced`. -/
theorem cliQuietKits_placed_fsOk_of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H)
    {kit : SessionStoreSpec A.repAlloc 0#64} {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (hq : kit.Quiet ∧ ikit.Quiet) :
    KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) :=
  KitFsOk.of_sound hq (hh.fs (lsProg_463 H) 463)

/-- Placed CLI budget `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `IdOrDistinctSid`) on `lsProg_463` for arbitrary kits. -/
theorem decryptSignalWithStores_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_placed hH (DecCalleesTPFPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Variant of `decryptSignalWithStores_placed_okVTP_fs_cli` transferring `DecCalleesTPPlaced_trap` via `TrapsOnly`. -/
theorem decryptSignalWithStores_placed_okVTP_fs_cli_of_trap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced_trap W.C A lim ctl S tdEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_placed hH (decCalleesTPFPlaced_of_trTrap_cli mmpl gh W hC) hQ hKitFs

/-- Placed CLI budget `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `DistinctSid`) on `lsProg_463` for arbitrary kits. -/
theorem decryptSignalWithStores_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_placed hH
    (DecCalleesTPFPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Variant of `decryptSignalWithStores_placed_okVTP_distinct_fs_cli` transferring `DecCalleesTPPlaced_trap` via `TrapsOnly`. -/
theorem decryptSignalWithStores_placed_okVTP_distinct_fs_cli_of_trap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hC : DecCalleesTPPlaced_trap W.C A lim ctl S tdEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_placed hH (decCalleesTPFPlaced_of_trTrap_cli mmpl gh W hC) hQ hKitFs

/-- Placed CLI budget `decrypt_signal` (`withStoresDecPlacedSpecVT`, `Scope ⊆ RecordInScope`) on `lsProg_463` for arbitrary kits. -/
theorem decryptSignalWithStores_placed_okVT_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecT W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVT W.C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVT_fs_placed hH hscopeIn
    (DecCalleesTFPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Concrete file-kit placed CLI budget `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `IdOrDistinctSid`). -/
theorem cliDecryptSignalWithStores_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
          encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_placed_okVTP_fs_cli mmpl gh W
    (decHypsExtPlaced_of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- Concrete file-kit placed CLI budget `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `DistinctSid`). -/
theorem cliDecryptSignalWithStores_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
          encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_placed_okVTP_distinct_fs_cli mmpl gh W
    (decHypsExtPlaced_of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- Variant of `cliDecryptSignalWithStores_placed_okVTP_fs_cli` taking `RunHooksPlaced` directly. -/
theorem cliDecryptSignalWithStores_placed_okVTP_fs_of_runHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
          encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_placed_okVTP_fs_cli mmpl gh W
    (decHypsExtPlaced_of_runHooks mmpl gh W hh hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk_of_runHooks hh hq)

/-- Variant of `cliDecryptSignalWithStores_placed_okVTP_distinct_fs_cli` taking `RunHooksPlaced` directly. -/
theorem cliDecryptSignalWithStores_placed_okVTP_distinct_fs_of_runHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
          encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_placed_okVTP_distinct_fs_cli mmpl gh W
    (decHypsExtPlaced_of_runHooks mmpl gh W hh hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk_of_runHooks hh hq)

/-- `withLsFrozen`-guarded placed CLI budget `decrypt_signal` (`IdOrDistinctSid`) on `lsProg_463`. -/
theorem decryptSignalWithStores_frozen_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv encRecord
            kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTP_frozen_fs_placed
    hH
    (LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.DecCalleesTPFFrozenPlaced.of_region
      hH.hooks.dealloc hreg)
    hQ hKitFs

/-- `withLsFrozen`-guarded placed CLI budget `decrypt_signal` (`DistinctSid`) on `lsProg_463`. -/
theorem decryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A lim uuidTryParse S encRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) kit kitEnv ikit ikitEnv st0 Scope)
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv encRecord
            kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDec_okVTP_distinct_frozen_fs_placed
    hH
    (LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.DecCalleesTPFFrozenPlaced.of_region
      hH.hooks.dealloc hreg)
    hQ hKitFs

/-- `withLsFrozen`-guarded concrete file-kit placed CLI budget `decrypt_signal` (`IdOrDistinctSid`). -/
theorem cliDecryptSignalWithStores_frozen_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
            encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_frozen_placed_okVTP_fs_cli mmpl gh W
    (decHypsExtPlaced_of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- `withLsFrozen`-guarded concrete file-kit placed CLI budget `decrypt_signal` (`DistinctSid`). -/
theorem cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
            encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli mmpl gh W
    (decHypsExtPlaced_of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- Variant of `cliDecryptSignalWithStores_frozen_placed_okVTP_fs_cli` taking `RunHooksPlaced` directly. -/
theorem cliDecryptSignalWithStores_frozen_placed_okVTP_fs_of_runHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
            encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
          (fun p => IdOrDistinctSid uuidTryParse kit st0 Scope p.1))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_frozen_placed_okVTP_fs_cli mmpl gh W
    (decHypsExtPlaced_of_runHooks mmpl gh W hh hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk_of_runHooks hh hq)

/-- Variant of `cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli` taking `RunHooksPlaced` directly. -/
theorem cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
        (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A lim ctl uuidTryParse S tdEnv
            encodeRecord kit kitEnv ikit ikitEnv st0 ist0 Scope)).restrictPre
          (fun p => DistinctSid uuidTryParse p.1.loc.name.bytes p.1.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli mmpl gh W
    (decHypsExtPlaced_of_runHooks mmpl gh W hh hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk_of_runHooks hh hq)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
