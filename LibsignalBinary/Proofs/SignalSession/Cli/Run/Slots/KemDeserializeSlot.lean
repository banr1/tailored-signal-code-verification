/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize

/-!
# `kem::Key<Public>::deserialize` Slot Adapter

Establishes `(slotsOf A img S needs).kemDeserialize.Ok img ext kemDeserializeName` from
`RunProofs.cliKemDeserialize_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-- `kem::Key<Public>::deserialize` satisfies `(slotsOf A img S needs).kemDeserialize`. -/
theorem hc_kemDeserialize {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {S : RunSem} {needs : RunNeeds}
    (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec) :
    (slotsOf A img S needs).kemDeserialize.Ok img ext kemDeserializeName :=
  fun stk hstk hstk63 =>
    RunProofs.cliKemDeserialize_ok hA hRO stk hstk (Nat.le_trans hstk63 (by decide))

theorem hc_kemDeserialize_of_hooks {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {S : RunSem} {needs : RunNeeds}
    (hh : RunHooks img A ext) :
    (slotsOf A img S needs).kemDeserialize.Ok img ext kemDeserializeName :=
  hc_kemDeserialize hh.alloc hh.memcpyRO

end CryptoVerification.SignalSession.Cli.RunCompose
