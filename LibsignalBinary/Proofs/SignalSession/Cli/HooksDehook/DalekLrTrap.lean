/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap -- proof-setup: allow-public-import

/-!
# Closed-`lr` Trap Suite Barrel for the Three Dalek Leaf Rows (`HooksDehook.DalekLrTrap`)

Re-exports the complete Card **D-d** (`dd_dalek_lrtrap.md`) closed-`lr` trap and `SubroutineOutcome`
suite for all three dalek leaf rows:
1. `HooksDehook.ZeroizeLrTrap`: Row 1 (`<StaticSecret as Drop>::drop`, `zeroize32Words`, `63` w =
   `252` B) region, classifier, `TrapHook` instances (for both Row 1 & Row 2), and Row 1 card-`c`
   post-hook / at-stub corollaries + Row 2 region & classifier.
2. `HooksDehook.SharedSecretDropLrTrap`: Row 2 (`<SharedSecret as Drop>::drop`,
   `sharedSecretDropHullWords`, `64` w = `256` B at `m`, hooked entry `m + sharedSecretDropEntryOff`)
   card-`c` post-hook / at-stub corollaries & entry-excluded `f3EmptySharedSecretDropGhostHook{,K}`
   wrappers (`entries = [m + sharedSecretDropEntryOff]`, never excluding unhooked `m`).
3. `HooksDehook.BlackBoxLrTrap`: Row 3 (`subtle::black_box::<u8>`, `blackBoxU8Words`, `5` w = `20` B)
   region, classifier, `TrapHook` instances, and card-`c` post-hook / at-stub corollaries.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekLrTrap

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekLrTrap
