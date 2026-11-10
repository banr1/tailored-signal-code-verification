/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded Callee Skeleton for `signal_session::run` (Placed)

Defines precondition-only and two-sided `FdsGe3Closed` spec and slot combinators
(`withPreFdsGe3Closed`, `slotWithPreFdsGe3Closed`, `slotWithFdsGe3Closed`,
`slotsWithPreFdsGe3Closed`) and the `RunCalleesPlacedFd` callee bundle for Block `579`
(`signal_session::run`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd

open Arm64
  (Program SepProp Spec State satisfies_pure_sepConj sepConj_assoc subroutine_ok subroutine_ok_mono)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553 blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (CalleeSlot CalleeSlot.OkPlaced RunBudgets RunSlots runNeed splitIdNeed splitSignedNeed)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudgetFd
  (cliDropSpe_placed_caller_ok_x_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
  (splitIdSpecPlacedOkFs subroutine_ok_splitIdSpecPlaced_of_okFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
  (splitSignedSpecPlacedOkFs subroutine_ok_splitSignedSpecPlaced_of_okFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (dropSpeSpecStkPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (bundleReadSpecPlaced dirGetSpecPlaced readFileSpecPlaced splitIdSpecPlaced splitSignedSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)

/-! ## `FdsGe3Closed` spec and slot combinators -/

/-- Strengthens `spec.pre` with `⌜FdsGe3Closed s0.fs⌝`, leaving `post`, `onPanic`, and `onOom` unchanged. -/
def withPreFdsGe3Closed {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => ⌜FdsGe3Closed s0.fs⌝ ∗ spec.pre x s0 }

theorem extract_withPreFdsGe3Closed {α : Type} {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withPreFdsGe3Closed spec).pre x s0 ∗ R) :
    FdsGe3Closed s0.fs ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withPreFdsGe3Closed] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

theorem subroutine_ok_withPreFdsGe3Closed_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withPreFdsGe3Closed spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hpre => (extract_withPreFdsGe3Closed hpre).2)
    (fun _ _ _ _ hpost => hpost)

theorem subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withFdsGe3Closed spec)) :
    subroutine_ok prog entry (withPreFdsGe3Closed spec) := by
  refine subroutine_ok_mono h (fun _ _ _ hpre => hpre) ?_
  intro x R s0 sf hpost
  dsimp only [withFdsGe3Closed, withPreFdsGe3Closed] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- Precondition-only `FdsGe3Closed` wrapper on a `CalleeSlot`. -/
def slotWithPreFdsGe3Closed (σ : CalleeSlot) : CalleeSlot :=
  { σ with spec := fun stk => withPreFdsGe3Closed (σ.spec stk) }

/-- Two-sided `FdsGe3Closed` wrapper on a `CalleeSlot`. -/
def slotWithFdsGe3Closed (σ : CalleeSlot) : CalleeSlot :=
  { σ with spec := fun stk => withFdsGe3Closed (σ.spec stk) }

theorem okPlaced_slotWithPreFdsGe3Closed_of_plain {callerProg : Program} {target : BitVec 64}
    {σ : CalleeSlot} (h : σ.OkPlaced callerProg target) :
    (slotWithPreFdsGe3Closed σ).OkPlaced callerProg target :=
  fun stk hlo hhi => subroutine_ok_withPreFdsGe3Closed_of_plain (h stk hlo hhi)

theorem okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed
    {callerProg : Program} {target : BitVec 64} {σ : CalleeSlot}
    (h : (slotWithFdsGe3Closed σ).OkPlaced callerProg target) :
    (slotWithPreFdsGe3Closed σ).OkPlaced callerProg target :=
  fun stk hlo hhi => subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed (h stk hlo hhi)

/-- Applies `slotWithPreFdsGe3Closed` to the four protocol slots (`encrypt`, `decryptSignal`,
`initiate`, `decryptPrekey`), leaving `kemDeserialize` unchanged. -/
def slotsWithPreFdsGe3Closed (slots : RunSlots) : RunSlots :=
  { encrypt := slotWithPreFdsGe3Closed slots.encrypt
    decryptSignal := slotWithPreFdsGe3Closed slots.decryptSignal
    initiate := slotWithPreFdsGe3Closed slots.initiate
    decryptPrekey := slotWithPreFdsGe3Closed slots.decryptPrekey
    kemDeserialize := slots.kemDeserialize }

theorem runNeed_slotsWithPreFdsGe3Closed (B : RunBudgets) (slots : RunSlots) :
    runNeed B (slotsWithPreFdsGe3Closed slots) = runNeed B slots :=
  rfl

/-! ## `RunCalleesPlacedFd` and projections -/

/-- `FdsGe3Closed`-threaded callee contracts for `signal_session::run` (Block `579`, `lsProg_579 ext`). -/
structure RunCalleesPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (cEnvs : RunCalleesEnvs)
    (ext : LibsignalHooks) (B : RunBudgets) (σ : RunSlots) : Prop where
  /-- `read_file` at the stub (`lsReadFileSym`), guarded by `LsRetAddr624 lr` in `pre` and
  carrying `FdsGe3Closed` in `pre` and `post`. -/
  readFile : subroutine_ok (lsProg_579 ext) (lsρ lsReadFileSym)
    (withLsRetAddr624AndFds
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile cEnvs.readFile))
  /-- `Dir::get` (`<signal_session::stores::Dir>::get`, Block `589`) with `FdsGe3Closed`. -/
  dirGet : ∀ {stk : Nat}, B.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim cEnvs.dirGet stk))
  /-- `read_bundle::{closure#0}` (Block `563`) with `FdsGe3Closed`. -/
  bundleRead : ∀ {stk : Nat}, B.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 563)
      (withFdsGe3Closed (bundleReadSpecPlaced cliIo.rd cliWrOk A lim cEnvs.bundleRead stk))
  /-- `split_id` (Block `593`) with Ok-only `fs` preservation (`splitIdSpecPlacedOkFs`). -/
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim cEnvs.splitId stk)
  /-- `split_signed` (Block `592`) with Ok-only `fs` preservation (`splitSignedSpecPlacedOkFs`). -/
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 ext) (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim cEnvs.splitSigned stk)
  /-- `drop_glue<SPE> [local#4]` fixed-stack contract (Block `553`). -/
  dropSpeX : subroutine_ok (lsProg_579 ext) (blkPl_553).base
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  /-- `drop_glue<SPE> [local#4]` arbitrary-stack contract (Block `553`). -/
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 ext) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  /-- `signal_session_ratchet::encrypt` (Block `464`), pre-guarded by `FdsGe3Closed`. -/
  encrypt : (slotWithPreFdsGe3Closed σ.encrypt).OkPlaced (lsProg_579 ext) (lsmpl.base 464)
  /-- `signal_session_ratchet::decrypt_signal` (Block `463`), pre-guarded by `FdsGe3Closed`. -/
  decryptSignal :
    (slotWithPreFdsGe3Closed σ.decryptSignal).OkPlaced (lsProg_579 ext) (lsmpl.base 463)
  /-- `signal_session_handshake::initiate` (Block `521`), pre-guarded by `FdsGe3Closed`. -/
  initiate : (slotWithPreFdsGe3Closed σ.initiate).OkPlaced (lsProg_579 ext) (lsmpl.base 521)
  /-- `signal_session_handshake::decrypt_prekey` (Block `520`), pre-guarded by `FdsGe3Closed`. -/
  decryptPrekey :
    (slotWithPreFdsGe3Closed σ.decryptPrekey).OkPlaced (lsProg_579 ext) (lsmpl.base 520)
  /-- `kem::Key<Public>::deserialize` (Block `590`), two-sided `withFdsGe3Closed`. -/
  kemDeserialize :
    (slotWithFdsGe3Closed σ.kemDeserialize).OkPlaced (lsProg_579 ext) (blkPl_590).base

theorem RunCalleesPlacedFd.splitIdPlain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {cEnvs : RunCalleesEnvs}
    {ext : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    (hc : RunCalleesPlacedFd A lim cEnvs ext B σ) {stk : Nat} (h : splitIdNeed ≤ stk) :
    subroutine_ok (lsProg_579 ext) (lsmpl.base 593)
      (splitIdSpecPlaced A lim cEnvs.splitId stk) :=
  subroutine_ok_splitIdSpecPlaced_of_okFs (hc.splitId h)

theorem RunCalleesPlacedFd.splitSignedPlain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {cEnvs : RunCalleesEnvs}
    {ext : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    (hc : RunCalleesPlacedFd A lim cEnvs ext B σ) {stk : Nat} (h : splitSignedNeed ≤ stk) :
    subroutine_ok (lsProg_579 ext) (lsmpl.base 592)
      (splitSignedSpecPlaced A lim cEnvs.splitSigned stk) :=
  subroutine_ok_splitSignedSpecPlaced_of_okFs (hc.splitSigned h)

/-- Fixed-stack `.keepsFs` contract for `drop_glue<SignalProtocolError>` (Block `553`) on any caller
block `i < 619`. -/
theorem dropSpeXFs_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks} [IsLsBlockProg callerProg i ext]
    (hh : RunHooksPlaced A lim ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_553).base
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim).keepsFs) :=
  cliDropSpe_placed_caller_ok_x_fs hh.allocFs hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
