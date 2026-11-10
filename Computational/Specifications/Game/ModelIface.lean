/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.GenericGame
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds

/-!
# The model interface `Σ_model^H` and the `KeyInd` experiment over a chosen handshake

**Trusted: the statement.** Read with `Computational/Specifications/Game/GenericGame.lean` and
`Computational/Specifications/Reductions/Pqxdh/StatementPqReds.lean`. See
`Computational/docs/TRUSTED_BASE.md`.

Lemma 3 (`ModelSecure`, `Computational/Specifications/Composition/StatementModel.lean`) is stated
over an arbitrary handshake, represented as a `KeyInd` oracle handler
`ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)`
(the paper's `H`). This file defines the `KeyInd` game over `ki` and the composed-game interface
`modelIface` (`Σ_model^H`), which runs `ki` followed by the byte-level Double Ratchet + SPQR
session model on `GhostState Bytes`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

namespace CryptoVerification.E2E

/-! ## `KeyInd` experiment over `ki` -/

/-- PQXDH `KeyInd` experiment over an arbitrary `KeyInd` handler `ki`: samples a challenge bit
`secb`, runs `A` against `ki` from `KeyIndState.empty S secb`, and returns a uniform bit if
`allTestedSessionsFresh P` fails at game end or `(b' == secb)` otherwise. -/
def pqxdhKeyIndExpForHandshake (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (A : SignalPqxdh.KeyIndAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := SignalPqxdh.KeyIndState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SignalPqxdh.KeyIndState S) ProbComp) + ki
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  if !allTestedSessionsFresh P finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

/-- Distinguishing advantage `2 |Pr[win] - 1/2|` (`boolBias`) of `A` in
`pqxdhKeyIndExpForHandshake S P ki A`. -/
noncomputable def KeyIndAdvantageForHandshake (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (A : SignalPqxdh.KeyIndAdversary S) : ℝ≥0∞ :=
  𝒟[pqxdhKeyIndExpForHandshake S P ki A].boolBias

/-! ## Model-state E2E driver -/

/-- Model-state E2E driver over `BHE2EDrvState S ℓ` parameterized by the handshake handler `ki`:
forwards `KeyInd` queries allowed by `bhDrvKiQueryOk` (refusing `corruptIK u` while `u` responds to
a promoted no-OPK instance via `bhNoOpkRespPromoted`) and mirrors responses via `bhE2EMirror`,
promotes sessions on `startDR` via `compositionLocalStart ki`, and steps promoted instances via
`bhE2EStepLocalSm`. -/
def bhE2EDrvImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← liftM (compositionLocalStart ki C K (some σ.b) σ sid)
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← liftM (bhE2EStepLocalSm C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

section ModelIface

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

/-! ## Model interface -/

/-- Lift a `StateT D M` query implementation to `StateT D (StateT K M)` via lens `get` / `set`. -/
def flattenImpl {ι : Type} {spec : OracleSpec ι} {M : Type → Type} [Monad M] {D K : Type}
    (get : D → K) (set : D → K → D) (impl : QueryImpl spec (StateT D M)) :
    QueryImpl spec (StateT D (StateT K M)) := fun q =>
  StateT.mk fun d => StateT.mk fun k =>
    (fun p => (p, get p.2)) <$> (impl q).run (set d k)

/-- Reassociate `composedSpec S ℓ (GhostState Bytes)` into
`unifSpec + bhTargetGameSpec S ℓ (BitVec 512)`. -/
def modelReassoc :
    QueryImpl (composedSpec S ℓ (GhostState Bytes))
      (OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))) := fun q =>
  match q with
  | .inl (.inl (.inl n)) =>
    query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n)
  | .inl (.inl (.inr kq)) =>
    query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inr (.inl (.inl kq)))
  | .inl (.inr cq) =>
    query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inr (.inl (.inr cq)))
  | .inr dq =>
    query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inr (.inr dq))

def modelAdvRun (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool) :
    OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool :=
  simulateQ modelReassoc A

/-- Model interface `Σ_model^H` of `G(Σ)` over handshake handler `ki`, primitives `P`, session
crypto `C`, SPQR KEM `K`, and epoch cap `qep`, with leaked party state `GhostState Bytes`,
challenge bit in `BHE2EDrvState.b`, and `KeyInd` state mirrored in `BHE2EDrvState.st` from
`KeyIndState.empty S true`. -/
def modelIface (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : ComposedIface S ℓ where
  St := GhostState Bytes
  prims := P
  Drv := BHE2EDrvState S ℓ
  init b := { b := b, st := SignalPqxdh.KeyIndState.empty S true }
  impl _ := flattenImpl (fun d : BHE2EDrvState S ℓ => d.st) (fun d st => { d with st := st })
      (bhE2EDrvImplWith P ki C K qep decT encT) ∘ₛ modelReassoc
  won := bhE2EDrvWon

end ModelIface

end CryptoVerification.E2E
