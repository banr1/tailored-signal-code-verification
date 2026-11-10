/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Slice and Read-Only `.rodata` Helpers for Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.SliceHelpers`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_sepWPp_with_ro_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {ret : BitVec 64} {s : State} {ro P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hro : ∀ {m : Memory} {R : SepProp}, CodeOk m → (m ⊨ R) → (m ⊨ ro ∗ R))
    (hk : SepWPp (runProgPlaced H) ret s (ro ∗ P) Q Qp oom) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom := by
  intro R hm hL
  exact hk R (by simpa only [sepConj_assoc] using hro hinv hm) hL

end CryptoVerification.SignalSession.Cli.RunCompose
