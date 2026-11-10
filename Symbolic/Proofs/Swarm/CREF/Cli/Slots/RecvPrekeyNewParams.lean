/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Model Hook Bridge Re-Exports for Fresh Pre-Key Receive

Specializes `ModelHookBridge` and `tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge`
for fresh pre-key session decryption.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames.LibsignalSession (SignalMessage MessageType SessionState)
open CryptoVerification.E2E (PEParams pqxdhSpqrSession)
open DY.Libsignal (HwBytes)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (interpW)
open DY.Libsignal.Composed.Refinement.Cli (ModelAgree)
open Symbolic.Swarm.CREF.Cli

abbrev RpkModelHookBridge : ExternInterpretation → PEParams → Prop :=
  Symbolic.Swarm.CREF.Cli.ModelHookBridge

theorem rpkModelHookBridge_interpOfParams {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) :
    RpkModelHookBridge (interpOfParams interp P) P :=
  modelHookBridge_interpOfParams hagree

theorem tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_rpkBridge
    {interp : ExternInterpretation} {P : PEParams} (hb : RpkModelHookBridge interp P)
    (expected : Option HwBytes) (msg : SignalMessage)
    (ty : MessageType) (coins : BitVec 256)
    (st : SessionState HwBytes) :
    SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P) expected msg ty coins st =
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW (cryptoOf' interp)
        (interpW interp) (Symbolic.Swarm.CREF.Cli.pureSpqrOf interp) expected msg ty coins st :=
  tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge hb expected msg ty coins st

end Symbolic.Swarm.CREF.Cli.Slots
