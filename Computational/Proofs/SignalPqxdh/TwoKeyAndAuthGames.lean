/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Game
public import Computational.Specifications.Assumptions.KemCorrect

/-!
# Standalone two-key `KeyInd` and `Auth` games and shallow reduction families

**Checked by Lean.** Defines the standalone two-key `KeyInd` game (`pqxdhKeyIndExp`,
`KeyIndAdvantage`, DEV-PQ13), single-primitive assumptions (`GapDH` under DEV-PQ17, `SigEufCma`,
and first-message INT-CTXT query types), and shallow reduction-family bundles
(`KeyInd2KeyReductionFamily`, `AuthReductionFamily`). No theorem of `Computational/Theorems/`
imports this file; see `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-! ## Standalone cryptographic assumptions -/

/-- Adversary against the single-pair X25519 Gap-DH game (DEV-PQ17). -/
structure GapDhAdv where
  run    : Bytes → Bytes → OracleComp (PrimBaseSpec + gapDhOracleSpec) Bytes
  q_ddh  : Nat
  q_prim : Nat

def GapDhAdv.Bounded (A : GapDhAdv) : Prop :=
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => q.isRight = true) A.q_ddh) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isPrimQuery q = true) A.q_prim)

/-- Single-pair X25519 Gap-DH experiment with prime-order subgroup check via `pow8`. -/
noncomputable def gapDhExp (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pow8 : Bytes → Bytes) (A : GapDhAdv) : ProbComp Bool := do
  let u ← sampleScalar32
  let v ← sampleScalar32
  let U := P.x25519Base u
  let V := P.x25519Base v
  let ddhImpl : QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let Z ← simulateQ (primBaseImpl P + ddhImpl) (A.run U V)
  return (pow8 Z == pow8 (P.x25519 u V))

/-- Success probability of `A` in the single-pair X25519 Gap-DH game (DEV-PQ17). -/
noncomputable def GapDH (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pow8 : Bytes → Bytes) (A : GapDhAdv) : ℝ :=
  (𝒟[gapDhExp P isValidDhTriple pow8 A] {true}).toReal

/-- Oracle queries in the one-time first-message INT-CTXT experiment. -/
inductive AeadIntQuery where
  | encOnce  (ad pt : Bytes)
  | tryForge (ad ct : Bytes)
  deriving DecidableEq, Repr

/-- Oracle queries in the multi-key first-message INT-CTXT experiment. -/
inductive AeadMuIntQuery where
  | encOnce  (i : ℕ) (ad pt : Bytes)
  | tryForge (i : ℕ) (ad ct : Bytes)
  deriving DecidableEq, Repr

def isMuEncQuery : ((ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) → Prop
  | .inr (.encOnce _ _ _) => True
  | _                     => False

def isMuForgeQuery : ((ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) → Prop
  | .inr (.tryForge _ _ _) => True
  | _                      => False

/-- Adversary against XEdDSA EUF-CMA security. -/
structure SigEufCmaAdv where
  run    : Bytes → OracleComp (PrimBaseSpec + sigOracleSpec) (Bytes × Bytes)
  q_sig  : Nat
  q_prim : Nat

def SigEufCmaAdv.Bounded (A : SigEufCmaAdv) : Prop :=
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => q.isRight = true) A.q_sig) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isPrimQuery q = true) A.q_prim)

/-- XEdDSA EUF-CMA experiment with fresh 64-byte signing randomness per query. -/
noncomputable def sigEufCmaExp (P : Primitives) (A : SigEufCmaAdv) : ProbComp Bool := do
  let sk ← sampleScalar32
  let pk := P.sigPkGen sk
  let impl : QueryImpl sigOracleSpec (StateT (List Bytes) ProbComp) := fun (.sign m) => do
    let r ← liftM sampleRandom64
    let sig := P.sigSign sk m r
    modify (m :: ·)
    return sig
  let fullImpl := (primBaseImpl P).liftTarget
      (StateT (List Bytes) ProbComp) + impl
  let ((mStar, sigStar), signedMsgs) ← (simulateQ fullImpl (A.run pk)).run []
  return (P.sigVerify pk mStar sigStar && decide (mStar ∉ signedMsgs))

/-- EUF-CMA advantage against XEdDSA. -/
noncomputable def SigEufCma (P : Primitives) (A : SigEufCmaAdv) : ℝ :=
  (𝒟[sigEufCmaExp P A] {true}).toReal

/-! ## Standalone two-key `KeyInd` experiment -/

/-- Core two-key `KeyInd` experiment (`useRo = true` for `-D DH`, `useRo = false` for HNDL;
    DEV-PQ13), returning a uniform coin if any tested session is unfresh at the end of the game. -/
noncomputable def pqxdhKeyIndExpCore (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested ||
        isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested ||
        isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles finalSt.sessions r)
  if !allTestedClean then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

/-- Two-key real-or-random `DRKey` indistinguishability experiment (`useRo = true`). -/
noncomputable def pqxdhKeyIndExp (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  pqxdhKeyIndExpCore true S P A

/-- Advantage of `A` in `pqxdhKeyIndExp` (`boolBias` of the output). -/
noncomputable def KeyIndAdvantage (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[pqxdhKeyIndExp S P A].boolBias).toReal

end SignalPqxdh

namespace SignalPqxdh.Security

open SignalPqxdh

/-- Shallow reduction family for standalone two-key `KeyInd` (`pqxdhKeyIndExp`). -/
structure KeyInd2KeyReductionFamily (S : Setup) where
  sig  : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → SigEufCmaAdv
  shcr : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → KemShCrAdv
  gdh  : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhAdv

structure KeyInd2KeyReductionQueryBounds (S : Setup) (R : KeyInd2KeyReductionFamily S) : Prop where
  sig_bounded  : ∀ b A, (R.sig b A).Bounded
  shcr_bounded : ∀ b A, (R.shcr b A).Bounded
  gdh_bounded  : ∀ b A, (R.gdh b A).Bounded

/-- Shallow reduction family for two-key authentication and first-message privacy (`pqxdhAuthExp`). -/
structure AuthReductionFamily (S : Setup) where
  mk' ::
  sig  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → SigEufCmaAdv
  shcr : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → KemShCrAdv
  gdh  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → GapDhAdv
  ck   : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfCkAdv
  mk   : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfMsgKeysAdv
  cpa  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadIndCpaAdv
  int  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfHmacAdv

structure AuthReductionQueryBounds (S : Setup) (R : AuthReductionFamily S) : Prop where
  sig_bounded  : ∀ b A, (R.sig b A).Bounded
  shcr_bounded : ∀ b A, (R.shcr b A).Bounded
  gdh_bounded  : ∀ b A, (R.gdh b A).Bounded
  ck_bounded   : ∀ b A, (R.ck b A).Bounded
  mk_bounded   : ∀ b A, (R.mk b A).Bounded
  cpa_bounded  : ∀ b A, (R.cpa b A).Bounded
  int_bounded  : ∀ b A, (R.int b A).Bounded

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  KeyInd2KeyReductionFamily KeyInd2KeyReductionQueryBounds
  AuthReductionFamily AuthReductionQueryBounds
)

end SignalPqxdh
