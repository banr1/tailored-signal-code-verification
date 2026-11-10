/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRun
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCheck

/-!
# Receive Collision Absence for `EvictedChainSkippedKeyCli`

Proves `not_nextEventCollides_recv` on every `.recv` event of `EvictedChainSkippedKeyCli.trace` by
combining `not_nextEventCollides_recv_of_memo` with `not_bobStartCollides_clean` and
`not_recvCollisionOn_clean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvNoCollision

open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Explains)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRun
  (not_nextEventCollides_recv_of_memo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCheck
  (not_bobStartCollides_clean not_recvCollisionOn_clean)

theorem not_nextEventCollides_recv
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hnfe : ∀ g' ss' vis',
      ¬ Explains evictedI0 r S g' ss' vis'
          Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace)
    (hsplit : Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains evictedI0 r S g ss vis evs₁)
    (hrecv : ∃ peer, ev.cmd = .recv peer) :
    ¬ NextEventCollides evictedI0 r S g ss vis evs₁ ev :=
  not_nextEventCollides_recv_of_memo
    not_bobStartCollides_clean not_recvCollisionOn_clean
    r S g ss vis evs₁ ev evs₂ hfit hnfe hsplit hex hrecv

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvNoCollision
