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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded Outer Slot Reduction for `decrypt_signal` (Placed)

Connects `decSigSlotSpecPlacedOf (withFds A)` to `withFdsGe3Closed (decSigSlotSpecPlacedOf A)` and
`withPreFdsGe3Closed` when `lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt signalMessageAt)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost RunSem SlotCtx decResAt slotOut slotTrace withCodeOk)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (decSigSlotSpecBasePlaced decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (slotFramePlaced)

/-- Splits `⌜FdsGe3Closed s.fs⌝` out of `slotFramePlaced (withFds A)` when `lim.enforced = true`. -/
theorem slotFramePlaced_withFds_enforced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true) (st : M.σ) (ctx : SlotCtx) (s : State) :
    slotFramePlaced (withFds A) lim st ctx s =
      ⌜FdsGe3Closed s.fs⌝ ∗ slotFramePlaced A lim st ctx s := by
  unfold slotFramePlaced
  rw [withFds_pool_enforced A henf]
  dsimp only [withFds_repAlloc]
  sep_ac_rfl

def decSigSlotSpecPlacedOfFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SlotEnv : DecSigGhost → List AllocEvent → Prop)
    (S : RunSem) (stk : Nat) : Spec (DecSigGhost × M.σ) :=
  withFdsGe3Closed (decSigSlotSpecPlacedOf CodeOk A lim SlotEnv S stk)

abbrev decSigSlotSpecFrozenPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SlotEnv : DecSigGhost → List AllocEvent → Prop)
    (S : RunSem) (stk : Nat) : Spec (DecSigGhost × M.σ) :=
  withFdsGe3Closed (decSigSlotSpecFrozenPlaced A lim SlotEnv S stk)

/-- Converts `subroutine_ok` for `decSigSlotSpecPlacedOf` at `withFds A` to `withFdsGe3Closed` at `A` when `lim.enforced = true`. -/
theorem decSigSlotSpecPlacedOf_withFds_to_withFds [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    (CodeOk : Memory → Prop)
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (SlotEnv : DecSigGhost → List AllocEvent → Prop)
    (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecPlacedOf CodeOk (withFds A) lim SlotEnv S stk)) :
    subroutine_ok prog entry
      (withFdsGe3Closed (decSigSlotSpecPlacedOf CodeOk A lim SlotEnv S stk)) := by
  refine subroutine_ok_mono hok (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · dsimp only [withFdsGe3Closed, decSigSlotSpecPlacedOf, withCodeOk,
      decSigSlotSpecBasePlaced, withFds_repAlloc] at hpre ⊢
    rw [slotFramePlaced_withFds_enforced A henf]
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre
    sep_ac_rfl
  · dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    dsimp only [decSigSlotSpecPlacedOf, withCodeOk,
      decSigSlotSpecBasePlaced, withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨g', hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨e, hpost⟩
    rw [withFds_pool_enforced A henf] at hpost
    let Body : List AllocEvent → StoresGhost →
        Except (CryptoGames.LibsignalSessionApi.ApiError AddrVal Unit) (List (BitVec 8)) → SepProp :=
      fun evs' g'' e' =>
        ⌜SlotEnv x evs' ∧ slotTrace s0 sf ∧
            slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g'' e' s0 sf⌝ ∗
          storesAt A.repAlloc x.stores g'' ∗ decResAt A.repAlloc x.ret e' ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs' st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
    have hpost' : sf.mem ⊨ ⌜FdsGe3Closed sf.fs⌝ ∗ (Body evs g' e ∗ R) := by
      dsimp only [Body]
      refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hpost
      sep_ac_rfl
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hfds, hbody⟩
    refine ⟨hfds, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨e, hbody⟩

theorem decSigSlotSpecFrozenPlaced_withFds_to_withFds [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (SlotEnv : DecSigGhost → List AllocEvent → Prop)
    (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced (withFds A) lim SlotEnv S stk)) :
    subroutine_ok prog entry
      (withFdsGe3Closed (decSigSlotSpecFrozenPlaced A lim SlotEnv S stk)) :=
  decSigSlotSpecPlacedOf_withFds_to_withFds _ A henf SlotEnv S stk hok

theorem decSigSlotSpecFrozenPlaced_withFds_to_preFd [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (SlotEnv : DecSigGhost → List AllocEvent → Prop)
    (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced (withFds A) lim SlotEnv S stk)) :
    subroutine_ok prog entry
      (withPreFdsGe3Closed (decSigSlotSpecFrozenPlaced A lim SlotEnv S stk)) :=
  subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed
    (decSigSlotSpecFrozenPlaced_withFds_to_withFds A henf SlotEnv S stk hok)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
