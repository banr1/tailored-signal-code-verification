/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
import all Init.Data.String.Defs
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import Symbolic.Specifications.Concrete.MachineEvents

/-!
# Slash-Splitting Step Helper

Auxiliary unfolding lemma for `Arm64.splitSlash.go` on non-slash characters.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots

open DY.Libsignal (HwBytes)
open CryptoGames
open CryptoVerification.E2E
open CryptoVerification.SignalSession

set_option linter.auxLemma false in
private theorem splitSlash_go_cons_ne (cur : List Char) {c : Char} (hc : c ≠ '/') (cs : List Char) :
    Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
  delta Arm64.splitSlash.go
  dsimp only [List.brecOn, List.brecOn.go, PProd.fst, PProd.snd]
  delta Arm64.splitSlash.go._f Arm64.splitSlash.go.match_1
  dsimp only
  split
  · next h => exact absurd h hc
  · rfl

end Symbolic.Swarm.CREF.Cli.Slots
