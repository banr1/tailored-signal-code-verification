/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Game
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH Game Helpers and Query-Bound Projections

**Checked by Lean.**

Defines the `wordsToDRKey` word-triple conversion helper and projections from `QueryBounded` onto
its per-oracle query bounds for the PQXDH key-indistinguishability and authentication games.
-/

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Convert a 96-byte word triple `(BitVec 256 × BitVec 256 × BitVec 256)` to a `DRKey`. -/
def wordsToDRKey (w : BitVec 256 × BitVec 256 × BitVec 256) : DRKey :=
  { rootKey  := word256ToBytes w.1
    chainKey := word256ToBytes w.2.1
    pqrKey   := word256ToBytes w.2.2 }

end SignalPqxdh

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

theorem QueryBounded.keyInd_total {S : Setup} {A : KeyIndAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) :
    OracleComp.IsQueryBoundP A.run (fun q => isGameQuery q = true) b.q_total := h.2.2.2.1

theorem QueryBounded.keyInd_on {S : Setup} {A : KeyIndAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) :
    OracleComp.IsQueryBoundP A.run isKeyIndOnlineQuery b.q_on := h.2.2.2.2

theorem QueryBounded.auth_ro {S : Setup} {A : AuthAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) : OracleComp.IsQueryBoundP A.run isAuthRoQuery b.q_ro := h.1

theorem QueryBounded.auth_send {S : Setup} {A : AuthAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) : OracleComp.IsQueryBoundP A.run isAuthSendQuery S.N_send_tot := h.2.1

theorem QueryBounded.auth_recv {S : Setup} {A : AuthAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) : OracleComp.IsQueryBoundP A.run isAuthRecvQuery S.N_recv_tot := h.2.2.1

theorem QueryBounded.auth_roRoot {S : Setup} {A : AuthAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) :
    OracleComp.IsQueryBoundP A.run isAuthRoRootQuery b.q_roRoot := h.2.2.2.1

theorem QueryBounded.auth_total {S : Setup} {A : AuthAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) :
    OracleComp.IsQueryBoundP A.run (fun q => isGameQuery q = true) b.q_total := h.2.2.2.2.1

theorem QueryBounded.auth_on {S : Setup} {A : AuthAdversary S} {b : QueryBudget}
    (h : QueryBounded A b) :
    OracleComp.IsQueryBoundP A.run isAuthOnlineQuery b.q_on := h.2.2.2.2.2

end SignalPqxdh
