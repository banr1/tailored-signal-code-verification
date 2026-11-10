/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPq
public import Computational.Specifications.Game.StatementPqOomFlag
public import VCVio.EvalDist.ProbabilityNotation
public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind

/-!
# Input-logged CLI security game

**Trusted: the statement.** Instantiates the monadic CLI game driver `Dir.cliDrvImplM`
(`StatementPq.lean`) in `WriterT (List Inputs) ProbComp` via `StatementPqOomFlag.lean` so every
`Inputs` record passed to `run` is appended to the writer log without classical `decide` inside
`ProbComp`. Because `WriterT` sits beneath the game's `StateT` layers, logged inputs persist across
calls that reject or leave party state unchanged. See `Computational/docs/TRUSTED_BASE.md`.

For any predicate `bad : Inputs → Prop`, `CliPqxdhFlagProb` is the probability under the logged
experiment `cliPqxdhExpFlagged` that some call `run i` satisfies `bad` (used for excused aborts in
`StatementPqElf.lean`). On the same log, `CliKemFailProb` is the probability that some ordered pair
of logged 64-byte coins tapes forms a failing honest ML-KEM-768 exchange (`MlKem.KemFailBad`),
which bounds adversary-chosen send randomness directly in the CLI game.
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.SignalSession

/-- Append `[i]` to the `WriterT` log and return `run i`. -/
def cliRunLogged (run : CliRun) (i : Inputs) : WriterT (List Inputs) ProbComp (Option Outcome) := do
  MonadWriter.tell [i]
  return run i

/-- Run `A` against `Dir.cliDrvImplM` over `WriterT (List Inputs) ProbComp` with `cliRunLogged run`
from the empty driver state. -/
def runCliDriverLogged (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvM S l)) (mode : BHDrvMode S)
    (A : CliGameAdversary S l (BitVec 512)) :
    StateT (SignalPqxdh.KeyIndState S) (WriterT (List Inputs) ProbComp)
      (Bool × CliDriverState S l) :=
  (simulateQ (Dir.cliDrvImplM S l P (cliRunLogged run) W qep decT encT
    (liftQueryImplStateT2 (n := WriterT (List Inputs) ProbComp) ext) mode) A.run).run {}

/-- Input-logged counterpart of `cliPqExp` in `ProbComp (Bool × List Inputs)`. -/
def cliPqxdhExpFlagged (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : Nat) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (A : CliGameAdversary S l (BitVec 512)) :
    ProbComp (Bool × List Inputs) :=
  WriterT.run do
    let P := modelPrims X W
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let ((b', ds), st) ←
      (runCliDriverLogged S l P run W qep decT encT bhNoExtWithSpqr (fun _ _ _ _ _ => some b)
        A).run (SignalPqxdh.KeyIndState.empty S true)
    if !allTestedSessionsFresh P st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b)

/-- Probability under `cliPqxdhExpFlagged` that at least one logged `run` input satisfies `bad`. -/
noncomputable def CliPqxdhFlagProb (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) (bad : Inputs → Prop) : ℝ≥0∞ :=
  Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[∃ i ∈ z.2, bad i]

/-! ## ML-KEM failure probability -/

/-- Contents of the last `coinsFile` entry in `i` (the entry read by the binary: 64 bytes on
`send`, 32 on `recv`, 192 on `init`), or `none` if absent. -/
def cliCoinsTape? (i : Inputs) : Option (List (BitVec 8)) :=
  (i.files.reverse.find? (·.1 == coinsFile)).map (·.2)

/-- Probability in `cliPqxdhExpFlagged` that some ordered pair of logged 64-byte coins tapes forms
a failing honest ML-KEM-768 exchange for `W.Q.K` (`MlKem.KemFailBad`). -/
noncomputable def CliKemFailProb (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) : ℝ≥0∞ :=
  Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT
      A}[W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true]

/-! ## Faithfulness and vanishing-bad-event properties -/

/-- Projecting `cliPqxdhExpFlagged` onto its Bool outcome recovers the distribution of `cliPqExp`. -/
def CliPqxdhExpFlaggedFaithful : Prop :=
  ∀ {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (l qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)),
    𝒟[Prod.fst <$> cliPqxdhExpFlagged S run X W l qep decT encT A] =
      𝒟[cliPqExp S run X W l qep decT encT A]

/-- `CliPqxdhFlagProb` vanishes whenever `bad` holds on no input. -/
def CliPqBadProbVanishes : Prop :=
  ∀ {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (l qep : Nat) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) (bad : Inputs → Prop),
    (∀ i, ¬ bad i) → CliPqxdhFlagProb S run X W l qep decT encT A bad = 0

end CryptoVerification.E2E
