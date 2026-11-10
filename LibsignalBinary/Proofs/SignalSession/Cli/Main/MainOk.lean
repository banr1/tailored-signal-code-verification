/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees

/-!
# End-to-End Composition Statement `main_ok` for `signal-session` `main`

States the composed `mainSpec` refinement obligation (`MainIoFacts` and `main_ok` inputs, proved in
`Cli/Main/Proofs/MainOkProof.lean`) over `Obj.Loads libsignalSessionImage img`, `MainCallees`,
`MainIo`, `MainIoFacts`, `runSpec` (`uuidTryParse`), domain `argv` parsing, and the 8 MiB initial
stack budget (`DEV-CLI7`).
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- File-system facts connecting `IoModel` to `initFsState (cliInputs i)` and `writeAll`. -/
structure MainIoFacts (io : IoModel) : Prop where
  /-- `read_stdin` reads `i.stdin` on the initial file system. -/
  stdin : ∀ i, CliInputsOk i → io.stdin (initFsState (cliInputs i)) = some i.stdin
  /-- `"coins"` is a modelled path. -/
  coinsPath : io.pathOk (utf8 "coins")
  /-- `read_file("coins")` returns `coinsOf i`, or `Err` when `¬ CoinsReadable i`. -/
  coins : ∀ i, CliInputsOk i → ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
    r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)
  /-- Sequential `commitFiles io.wr` on modelled paths satisfying `WriteOk` agrees with `writeAll`. -/
  commit : ∀ i, CliInputsOk i → ∀ ws : List (List (BitVec 8) × List (BitVec 8)),
    (∀ pw ∈ ws, io.pathOk pw.1) →
    (∀ pw ∈ namedWrites ws, WriteOk i pw.1) →
    commitFiles io.wr (initFsState (cliInputs i)).files ws =
      some (MainPost.writeAll (initFsState (cliInputs i)) (namedWrites ws)).files

end CryptoVerification.SignalSession.Cli.MainHops
