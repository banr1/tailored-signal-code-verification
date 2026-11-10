/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore

/-!
# End-to-end composition reduction bundles and per-session mixture bound

**Trusted: definitions used by the statement.** This file defines the multi-session composition
`ReductionDsl` bundles and per-session mixture bound used by `ModelSecure`
(`Computational/Specifications/Composition/StatementModel.lean`) and `CliPqxdhSecurityFor`
(`Computational/Specifications/LibsignalCli/StatementPqElf.lean`). See
`Computational/docs/TRUSTED_BASE.md`.

A `CompositionCostedReductions` bundle reduces the multi-session game `bhTargetGameSpec` to
one-key real-HKDF PQXDH key indistinguishability (`kindRed`) and to single-session ACD19 secure
messaging (`prefixRed k` for session `k`), using operations from `ReductionDsl.atomicE2EOps` and
coin-only randomness from `ReductionDsl.atomicBaseSamplers`. `CompositionCostedReductionsBounded`
bounds both uniform step cost (`bhE2ECostBudget`) and per-query-kind step cost
(`bhE2ECostBudgetByKind`, separating online protocol queries from offline random-oracle queries via
`bhQueryKind`). For each session `k`, `bhPrefixFullBoundMixV1With` combines the single-session
bound `uniformStartMixtureBound` over the stage-1 identity/pre-key distribution with the PRF, PRG,
forgery, collision, and scalar-guessing terms of the signed-pre-key hybrid hops.
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

/-- Local `startDR sid` promotion step on `BHE2EDrvState S ℓ` against handshake oracle `ki`, used by
the reference model game `modelIface`. -/
def compositionLocalStart {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × BHE2EDrvState S ℓ) := do
  match bhE2EGuard σ sid with
  | none => return (none, σ)
  | some (_, _, (u, j)) =>
    let (kr1, st1) ← (ki (.testSession sid)).run σ.st
    let (kr2, st2) ← (ki (.revealSpkSk u j)).run st1
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    return bhE2EFinishStartSpk C K bMode? { σ with st := st2 } sid kr1 kr2 ac

/-- Multi-session composition `ReductionDsl` bundle: a one-stage reduction `kindRed` to one-key
`KeyInd` and a family `prefixRed k` of two-stage reductions to single-session `SM.spec` with
stage-1 context `ReductionDsl.prefixCtxT`. -/
structure CompositionCostedReductions (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  kindRed :
    ReductionDsl.CostedReduction (ReductionDsl.atomicE2EOps ℓ P C K decT encT)
      (ReductionDsl.e2eKeyIndTargetIface S ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool .bool
  prefixRed : (k : ℕ) →
    ReductionDsl.TwoStageCostedReduction (ReductionDsl.atomicE2EOps ℓ P C K decT encT)
      (ReductionDsl.e2eSessionTargetIface ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool (ReductionDsl.prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool

/-- Family of `CompositionCostedReductions` indexed by handshake budget `b` and static loop bounds
`qStart`, `qDR`, and `qInst`. -/
abbrev CompositionCostedReductionFamily (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Type :=
  (b : SignalPqxdh.QueryBudget) → (qStart qDR qInst : ℕ) →
    CompositionCostedReductions S ℓ P C K qep decT encT

/-- Boundedness predicate for `R`: enforces size, size-honesty, target-query (`2 * qTot` for
`kindRed`, `qTot` for `prefixRed k`), and uniform step-cost bounds (`GRedBounded`, `GRed2Bounded`
against `bhE2ECostBudget`), together with per-kind step-cost and query bounds (`GRedCostByKind`,
`GRed2CostByKind` against `bhE2ECostBudgetByKind` under `bhQueryKind` and `bhKindCounts`). The
per-kind conjuncts separate online protocol queries (kind `0`) from offline `.roQuery` calls (kind
`1`) so offline hashes pay only random-oracle table lookup rather than online dispatch and
session-table scans. -/
def CompositionCostedReductionsBounded {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductions S ℓ P C K qep decT encT) : Prop :=
  let qDR := ∑ k ∈ Finset.range qStart, qs k
  let qInst := Finset.sup (Finset.range qStart) qs
  let qTot := b.q_total + qStart + qDR
  let B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
  let qKind := bhKindCounts b qStart qDR
  let qSum := (List.ofFn qKind).sum
  let Bk := bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ
  (GRedBounded R.kindRed (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B ∧
  (∀ k < qStart,
    GRed2Bounded (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot qTot B false)) ∧
  (GRedCostByKind R.kindRed (fun _ => 1) (fun _ => 0) bhQueryKind qKind (2 * qSum) Bk ∧
  (∀ k < qStart,
    GRed2CostByKind (R.prefixRed k) (fun _ => 1) (fun _ => 0) bhQueryKind qKind qSum Bk))

/-- Uniform `CompositionCostedReductionsBounded` compliance across all query budgets. -/
def CompositionCostedReductionFamilyBounded {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (reds : CompositionCostedReductionFamily S ℓ P C K qep decT encT) : Prop :=
  ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
    CompositionCostedReductionsBounded P C K qep decT encT b qStart qs
      (reds b qStart (∑ k ∈ Finset.range qStart, qs k) (Finset.sup (Finset.range qStart) qs))

/-- Per-session advantage bound for `R_e2e.prefixRed k` on adversary `B_A`: the sum of
`uniformStartMixtureBound` over stage-1 context `(idA, (idB, spkCoins))` and the signed-pre-key
hybrid PRF, PRG, forgery, collision, and scalar-guessing terms. -/
noncomputable def bhPrefixFullBoundMixV1With {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep qTot q : ℕ) (δ : ℝ≥0∞) (k : ℕ) (flip : Bool)
    (R_e2e : CompositionCostedReductions S ℓ P C K qep decT encT)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ℝ≥0∞ :=
  let oa := stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)
  let Ak := fun o => (R_e2e.prefixRed k).eval2 o.2 flip qTot false
  let R := fun o => D C K o.1.1 o.1.2.1 Dh encPt encT decT 0 qep q
  let Rspk := fun o => (R o).spk
  uniformStartMixtureBound C K ℓ Dh encPt encT decT 0 qep q δ oa
      (fun o => o.1.1) (fun o => o.1.2.1) R Ak
    + 2 * (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRed (Rspk o).spkLeakRed o.1.2.2 (Ak o)))
    + 2 * (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (Ak o))))
    + 2 * (epoch0ChainForgeryTerm C.F q
        + (∑ j ∈ Finset.range spkSwapHybridCount,
            ((Ratchet.expandPRG C.F).prgAdvantage
                (prefixPrgAvg oa (fun o =>
                  evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) o.1.2.2 (Ak o)))
              + (extractPRF C.F encPt).prfAdvantage
                (prefixPrfAvg oa (fun o =>
                  evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) o.1.2.2 (Ak o)))))
        + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q)

end CryptoVerification.E2E
