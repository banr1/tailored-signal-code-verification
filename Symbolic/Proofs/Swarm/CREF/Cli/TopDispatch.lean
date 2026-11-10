/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge

/-!
# Directory Invariant Initialization and Caller Dispatch

Specializes `pqDirInv_init` to `interpOfParams` and extracts the caller's `PqPartyInv` state,
domain invariant, and encoded session record for guarded CLI calls.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure

theorem pqDirInv_init_interpOfParams {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r) (hagree : ModelAgree interp P) :
    PqDirInv (interpOfParams interp P) P r
      (CliTurn.init (initDirs (interpOfParams interp P) r)) [] :=
  pqDirInv_init hr ((modelAgree_interpOfParams interp P).mpr hagree)

theorem pqDispatch_send_party {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {t : CliTurn} {c : CliCall}
    (hinv : PqDirInv interp P r t accepted) (hbca : BobCallAllowed r t c)
    (hp : c.party = r.alice ∨ c.party = r.bob) (hfb : FilesBounded (t.dirs c.party)) :
    ∃ st : PqParty,
      PqxdhPartyInSpecDomain P st ∧
      t.records r c.party = st.session.map (fun xg => encodeRecordUnderExtras (fun _ => xg.1) xg.2) ∧
      PqPartyInv interp P r accepted c.party st (t.dirs c.party) := by
  obtain ⟨_, st, hinvP⟩ := caller_pqPartyInv_of_allowed hinv hbca hp
  exact ⟨st, wfPq_of_pqPartyInv hinvP hfb, records_of_pqPartyInv hinvP, hinvP⟩

end Symbolic.Swarm.CREF.Cli
