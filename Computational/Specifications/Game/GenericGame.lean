/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore

/-!
# Generic multi-session composed security game `G(Σ)`

**Trusted: the statement.** Read with
`Computational/Specifications/Game/StatementBinaryHarnessCore.lean`, which defines the shared
oracle signatures, `KeyInd` state, and end-of-game freshness predicate. See
`Computational/docs/TRUSTED_BASE.md`.

Models the generic multi-session composed game `G(Σ)` (§4.2, `docs/PAPER_MAP.md`) as an experiment
`composedExp I A` over a protocol interface `I : ComposedIface S ℓ`. The adversary interacts with
PQXDH handshakes, promotes handshake sessions via `startDR`, and attacks promoted instances as
ACD19 secure-messaging (`SM.spec`) sessions. Two interfaces instantiate `ComposedIface`: the CLI
interface `cliIface` (`Σ_bin` in `Computational/Specifications/Game/StatementPq.lean`, fixed to the
binary-harness handshake `bhDrvKeyInd`) and the model interface `modelIface` (`Σ_model^H` in
`Computational/Specifications/Game/ModelIface.lean`, parameterized by a `KeyInd` handler `H`).

Independently of `I`, `composedExp` samples one challenge bit `b` shared across all promoted
ratchet instances, initializes `KeyIndState.empty S true` so `startDR` promotes real handshake
keys, checks `allTestedSessionsFresh I.prims` on the separate `KeyIndState` layer at the end of the
run (returning a uniform coin on failure), and otherwise wins on `b' == b || I.won d b`. That `I`
uses `b` solely for challenge queries is a property of each concrete `ComposedIface`, and query
budgets are imposed as theorem hypotheses.
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

/-- Per-instance secure-messaging oracle family of `G(Σ)` with leaked-state type `St`, indexed by
instance number (`cliGameDrSpec ℓ (BitVec 512)` at `St = BinState`). -/
@[reducible] def composedDrSpec (ℓ : ℕ) (St : Type) :
    OracleSpec (ℕ × (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) :=
  fun x => (SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range x.2

/-- Full adversary oracle signature in `G(Σ)`: uniform coins, `KeyInd`, `startDR`, and per-instance
secure-messaging oracles (`cliGameSpec S ℓ (BitVec 512)` at `St = BinState`). -/
abbrev composedSpec (S : SignalPqxdh.Setup) (ℓ : ℕ) (St : Type) :=
  unifSpec + SignalPqxdh.keyIndSpec S + bhDrCtlSpec S + composedDrSpec ℓ St

/-- Protocol interface `Σ` instantiating the composed game `G(Σ)`. -/
structure ComposedIface (S : SignalPqxdh.Setup) (ℓ : ℕ) where
  /-- State leaked upon party corruption. -/
  St : Type
  /-- Primitives used by the end-of-game `allTestedSessionsFresh` check. -/
  prims : SignalPqxdh.Primitives
  /-- Driver state tracking promoted instances and pending handshakes. -/
  Drv : Type
  /-- Initial driver state for challenge bit `b`. -/
  init : Bool → Drv
  /-- Oracle implementation for challenge bit `b` over `Drv` and `KeyIndState S`. -/
  impl : Bool → QueryImpl (composedSpec S ℓ St)
    (StateT Drv (StateT (SignalPqxdh.KeyIndState S) ProbComp))
  /-- Whether any promoted instance recorded an accepted forgery under challenge bit `b`. -/
  won : Drv → Bool → Bool

/-- Composed security experiment `G(Σ)`: runs `A` against `I.impl b` from `I.init b` and
`KeyIndState.empty S true` for uniform `b`, and returns a uniform coin if `allTestedSessionsFresh`
fails or `b' == b || I.won d b` otherwise. -/
def composedExp {S : SignalPqxdh.Setup} {ℓ : ℕ} (I : ComposedIface S ℓ)
    (A : OracleComp (composedSpec S ℓ I.St) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let ((b', d), st) ←
    ((simulateQ (I.impl b) A).run (I.init b)).run (SignalPqxdh.KeyIndState.empty S true)
  if !allTestedSessionsFresh I.prims st then $ᵗ Bool
  else return (b' == b || I.won d b)

/-- Distinguishing advantage `2 |Pr[composedExp I A = true] - 1/2|` of `A` in `G(Σ)`. -/
noncomputable def ComposedAdvantage {S : SignalPqxdh.Setup} {ℓ : ℕ} (I : ComposedIface S ℓ)
    (A : OracleComp (composedSpec S ℓ I.St) Bool) : ℝ≥0∞ :=
  𝒟[composedExp I A].boolBias

end CryptoVerification.E2E
