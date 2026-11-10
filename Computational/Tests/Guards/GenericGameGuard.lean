/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementPq

/-!
# Definitional Guard for `cliPqExp` and `composedExp`

**Checked by Lean.** Checks by `rfl` that instantiating the generic composed game `composedExp` at
`cliIface` yields the binary-harness oracle interface `cliGameSpec S l (BitVec 512)` on state
`BinState`, and that `cliPqExp` unfolds definitionally to the binary-harness experiment running
`Dir.runCliDriver`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.GenericGame

open CryptoVerification.E2E CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession CryptoGames.LibsignalSessionApi SM CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SignalSession OracleComp OracleSpec

example (S : SignalPqxdh.Setup) (l : ℕ) :
    composedSpec S l BinState = cliGameSpec S l (BitVec 512) := rfl

example (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : ℕ)
    {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliIface S run X W l qep decT encT).St = BinState := rfl

/-- `cliPqExp` unfolds definitionally to the binary-harness experiment driven by `run`. -/
theorem cliPqExp_eq_body (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : ℕ) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (A : CliGameAdversary S l (BitVec 512)) :
    cliPqExp S run X W l qep decT encT A = (do
      let P := modelPrims X W
      let b ← $ᵗ Bool
      let ((b', ds), st) ←
        (Dir.runCliDriver S l P run W qep decT encT bhNoExtWithSpqr (fun _ _ _ _ _ => some b) A).run
          (SignalPqxdh.KeyIndState.empty S true)
      if !allTestedSessionsFresh P st then $ᵗ Bool
      else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b)) := rfl

end CryptoVerification.E2E.Guards.GenericGame
