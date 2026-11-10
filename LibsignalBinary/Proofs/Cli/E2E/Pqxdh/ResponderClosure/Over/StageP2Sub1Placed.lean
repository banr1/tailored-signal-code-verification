/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1V4Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Stage P2 Over-Path Substage P2.1 Stack and Buffer Helpers

Lifts stack-budget inequalities, cell splits, and session-state projection lemmas for Stage P2
Substage P2.1 under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2

theorem p2_strToOwnedStack_le_overPure_placed [LibsignalPlacement] :
    Matched.strToOwnedLocal2Stack ≤ stageP2OverPureAndErrStack := by
  decide

theorem p2_cells48_le_overPure_placed [LibsignalPlacement] :
    48 ≤ stageP2OverPureAndErrStack := by
  decide

theorem p2_stackAt_48_cells6_placed [LibsignalPlacement] (sp : BitVec 64) :
    stackAt sp 48 = cells (sp - 48#64) 6 := by
  change memRegion (sp - 48#64) 48 = _
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem p2_sessionAt_entails_state_placed [LibsignalPlacement] (A : RustAlloc) (p : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionStateReprAt A p recG sess ⊢ sessionStateAt A p recG sess.state :=
  sessionAt_entails_sessionStateAt A p recG sess

theorem p2_sp3e0_24_rejoin_placed [LibsignalPlacement] (sp : BitVec 64)
    (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
      memRegion (sp + 0x3e9#64) 7 ∗ memRegion (sp + 0x3f0#64) 8 ⊢
    memRegion (sp + 0x3e0#64) 24 :=
  p2_sp3e0_24_rejoin sp w0 b8

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
end
