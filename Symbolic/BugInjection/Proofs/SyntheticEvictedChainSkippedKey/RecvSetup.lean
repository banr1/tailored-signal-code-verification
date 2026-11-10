/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws

/-!
# Setup and Trace Constants for `EvictedChainSkippedKeyCli`

Defines shorthand aliases `w0`, `trace0`, and `r0` for the `EvictedChainSkippedKeyCli` witness and
projects participant names and setup secrets from `evictedCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup

open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF PreKeyFields KyberMismatch setupTrace secretBytes)
open Symbolic.BugInjection (PQXDHSpqrSetup fillFresh)
open Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli (setup trace)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedRecordsI0 evictedCompFitsPinned)

abbrev w0 : PQXDHSpqrSetup := setup

abbrev trace0 : List CliEvent := trace

abbrev r0 : ProtocolSetup := evictedRecordsI0 w0

theorem trace0_length : trace0.length = 25 := by decide

theorem r_alice_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    r.alice = "alice" :=
  hfit.1.2.2.2.1.1

theorem r_bob_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    r.bob = "bob" :=
  hfit.1.2.2.2.1.2

theorem r_secret3_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    secretBytes r 3 = fillFresh 11 64 :=
  hfit.1.2.2.1.1

theorem r_secret4_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    secretBytes r 4 = fillFresh 16 64 :=
  hfit.1.2.2.1.2.1

theorem r_secret5_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    secretBytes r 5 = fillFresh 17 64 :=
  hfit.1.2.2.1.2.2

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
