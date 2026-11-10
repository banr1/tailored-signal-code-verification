/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoBobStart
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsB
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperAssembly

/-!
# Memo and MAC Collision Absence on Clean Prefixes

Exports `not_bobStartCollides_clean` (Call 3 `bobStart`) and `not_recvCollisionOn_clean`
(Calls `5, 7, ..., 23` and `24`) for any valid send-coin schedule `cls` (`ValidCoinLens`) and
SPQR receive indices `spqrIdxs` explaining `trace0.take k` under `evictedCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCheck

open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry PreKeyFields parsePreKeyWire
   runTrace honestSaltsOf Explains BobSessionStartCollidesOrImplicitRejectsOn RecvCollisionOn)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens whisperOrReplayIndices ssClean cleanPreKeyRep cleanRecvTerm)

/-- At Call 3 (`bobStart`), `cleanPreKeyRep r cls spqrIdxs` triggers no implicit rejection,
`MemoCollisionOn`, or `MacTagForgeryOrCollision` on `ssClean cls spqrIdxs 3`. -/
theorem not_bobStartCollides_clean
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (vis' : List VisEntry)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (p : PreKeyFields)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hcls : ValidCoinLens cls)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs 3) vis' (trace0.take 3))
    (hp : parsePreKeyWire (ev 3).input = some p) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn evictedI0 r S g'
        (runTrace r (ssClean cls spqrIdxs 3)) vis'
        (honestSaltsOf r (ssClean cls spqrIdxs 3)) p
        (cleanPreKeyRep r cls spqrIdxs) :=
  RecvMemoBobStart.not_bobStartCollides_clean r S g' vis' cls spqrIdxs p hfit hcls hExp hp

/-- At Calls `5, 7, ..., 23` and `24`, `cleanRecvTerm r cls spqrIdxs k` triggers neither
`MemoCollisionOn` nor `MacTagForgeryOrCollision` on `ssClean cls spqrIdxs k`. -/
theorem not_recvCollisionOn_clean
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (vis' : List VisEntry)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (k : Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hcls : ValidCoinLens cls)
    (hk : k ∈ whisperOrReplayIndices)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs k) vis' (trace0.take k)) :
    ¬ RecvCollisionOn evictedI0 r S g'
        (runTrace r (ssClean cls spqrIdxs k)) vis'
        (honestSaltsOf r (ssClean cls spqrIdxs k))
        (cleanRecvTerm r cls spqrIdxs k) :=
  RecvMemoWhisperAssembly.not_recvCollisionOn_of_new_chain_trials
    (@RecvMemoWhisperTrialsB.safeMemo_new_chain_trials)
    r S g' vis' cls spqrIdxs k hfit hcls hk hExp

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCheck
