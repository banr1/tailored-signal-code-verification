/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTracePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Trace and Exit Postcondition Packagers

Proves `dpPollPost_of_slotTraceFT_placed` packaging closure exit states and `A.pool` into
`dpPollSpecStateBudget.post` from `DecPkEnv`, `slotTraceFT`, and `slotOutTr`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTracePlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal pendingTag preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunSem decResAt decResAt_entails_dpWords_resHeap dpResHeap slotOutTr slotTraceFT)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt dpWordsAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)

private theorem pure_sepConj_intro_placed {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, emp_sepConj]
  exact h

/-- Packages `decResAt`, `storesAt`, preserved caller borrows, `A.pool lim (M.stepEvents evs y.st) sf`,
`dpFutDoneAt`, `memRegion cx 32`, `stackAt s0.sp stk'`, and any leftover heap `Leftover` into
`dpPollSpecStateBudget.post` at `dpSlotPollKStatePlaced A lim DecPkEnv B S` from `DecPkEnv y.g evs`,
`slotTraceFT`, and `slotOutTr`. -/
theorem dpPollPost_of_slotTraceFT_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem)
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 sf : State) (evs : List AllocEvent)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) Bytes)
    (Leftover : SepProp)
    (hevs : DecPkEnv y.g evs)
    (hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt A.repAlloc y.out e ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗
      A.pool lim (M.stepEvents evs y.st) sf ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf := by
  have hdec := decResAt_entails_dpWords_resHeap A.repAlloc y.out e
  have hany : Leftover ⊢ anyHeap := entails_anyHeap Leftover
  refine Entails.trans (sepConj_mono hdec
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hany)))))))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ws => ?_
  let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
  change (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws ∗ dpResHeap A.repAlloc ws e) ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
    (∃∗ ws', ⌜ws'.length = 6 ∧ ws'.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws' ∗ K.res y.g y.st s0 sf ws') ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk'
  have hreord :
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗ dpResHeap A.repAlloc ws e) ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' =
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗
        (storesAt A.repAlloc y.g.stores g' ∗ dpResHeap A.repAlloc ws e ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ anyHeap)) ∗
      (dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk') := by
    sep_ac_rfl
  rw [hreord]
  refine sepConj_mono_left (Entails.sepExists_right ws ?_)
  refine sepConj_mono_right (sepConj_mono_right ?_)
  dsimp only [K, dpSlotPollKStatePlaced]
  exact Entails.sepExists_right evs
    (Entails.sepExists_right g'
      (Entails.sepExists_right e
        (pure_sepConj_intro_placed ⟨hevs, hft, hout⟩ (Entails.refl _))))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTracePlacedBudget
