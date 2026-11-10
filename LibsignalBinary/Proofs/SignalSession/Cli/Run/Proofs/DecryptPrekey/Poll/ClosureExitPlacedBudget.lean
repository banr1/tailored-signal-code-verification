/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTracePlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Exit and Trace Packagers

Provides trace/filesystem preservation (`cliFiles_eq_of_trace_eq_placed`,
`cliSlotTraceFT_of_trace_eq_placed`) and `dpPollPost_of_decResAt_placed` under
`ClosureStagesStmtPlacedBudget.RunHooksPlaced A lim ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.LibsignalPublicApi.StoreKit (NoFsEv withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunSem decResAt slotOutTr slotTraceFT)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTracePlacedBudget
  (dpPollPost_of_slotTraceFT_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)

/-! ## 1. Trace & Exit Postcondition Packagers -/

theorem cliFiles_eq_of_trace_eq_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State}
    (hh : RunHooksPlaced A lim ext)
    (hst : Steps prog s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (hh.fs prog i).files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliSlotTraceFT_of_trace_eq_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State}
    (hh : RunHooksPlaced A lim ext)
    (hst : Steps prog s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  ⟨htr ▸ List.prefix_refl s0.trace,
   cliFiles_eq_of_trace_eq_placed hh hst htr,
   congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem dpPollPost_of_decResAt_placed [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 sf : State) (evs : List AllocEvent)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) Bytes)
    (Leftover : SepProp)
    (hevs : DecPkEnv y.g evs)
    (hh : RunHooksPlaced A lim ext)
    (hsteps : Steps prog s0 sf)
    (htr : sf.trace = s0.trace)
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
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf :=
  dpPollPost_of_slotTraceFT_placed A lim DecPkEnv B S stk' y s0 sf evs g' e Leftover hevs
    (cliSlotTraceFT_of_trace_eq_placed hh hsteps htr) hout

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlacedBudget
