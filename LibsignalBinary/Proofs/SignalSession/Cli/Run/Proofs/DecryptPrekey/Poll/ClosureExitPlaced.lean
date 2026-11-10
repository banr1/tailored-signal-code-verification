/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTracePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Poll Exit and Trace Packagers

Relocatable `[LibsignalPlacement]` trace preservation and `dpPollPost_of_decResAt_placed` exit
packaging lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Trace & Exit Postcondition Packagers -/

theorem cliFiles_eq_of_trace_eq_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State}
    (hh : RunHooksPlaced E2E.HooksE.A0 ext)
    (hst : Steps prog s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (hh.fs prog i).files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliSlotTraceFT_of_trace_eq_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State}
    (hh : RunHooksPlaced E2E.HooksE.A0 ext)
    (hst : Steps prog s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  ⟨htr ▸ List.prefix_refl s0.trace,
   cliFiles_eq_of_trace_eq_placed hh hst htr,
   congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem dpPollPost_of_decResAt_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 sf : State)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hh : RunHooksPlaced E2E.HooksE.A0 ext)
    (hsteps : Steps prog s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt E2E.HooksE.A0 y.out e ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).post y s0 sf :=
  dpPollPost_of_slotTraceFT_placed B S stk' y s0 sf g' e Leftover
    (cliSlotTraceFT_of_trace_eq_placed hh hsteps htr) hout

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
