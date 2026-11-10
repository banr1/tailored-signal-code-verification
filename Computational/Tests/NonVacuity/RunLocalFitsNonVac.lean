/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets

/-!
# Satisfiability of Run-Local Query-Size Premises

**Checked by Lean.**

Non-vacuity witnesses for the run-local query-size premise `ReductionDsl.AllGameQueriesFit B C`
used in `GRedBounded`, `GRed2Bounded`, `GRedBlockBounded`, and `GRed2BlockBounded`. Global
universally quantified bounds `∀ t, C.Q.Fits B (C.qenc t)` fail whenever a codec has an unbounded
field (`e2eSession_global_query_premise_false`). For each headline codec (`e2eSessionCodec`,
`fig8SmCodecDF`, `pqKeyIndCodec`, `authCodec`), `oneQuery` provides a one-query adversary that
satisfies `AllGameQueriesFit B C` for every `B`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.NonVacuity.RunLocalFits

open OracleSpec OracleComp
open CryptoGames ReductionDsl
open Ratchet LibsignalInst LibsignalSession LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM CKA
  FSAEAD

/-- Adversary that issues the single game query `t` and returns `false`. -/
def oneQuery {κ : Type} {G : OracleSpec κ} (t : κ) : OracleComp (unifSpec + G) Bool :=
  (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) : OracleComp (unifSpec + G) _) >>=
    fun _ => pure false

theorem oneQuery_fits {S : Sig} {κ : Type} {G : OracleSpec κ} (C : GameCodec S G) (B : ℕ)
    (t : κ) (h : C.Q.Fits B (C.qenc t)) : AllGameQueriesFit B C (oneQuery (G := G) t) := by
  show C.Q.Fits B (C.qenc t) ∧ ∀ _ : G t, True
  exact ⟨h, fun _ => trivial⟩

/-- `oneQuery t` satisfies game-query bound `1` and not `0`. -/
theorem oneQuery_bound {κ : Type} {G : OracleSpec κ} (t : κ) :
    (oneQuery (G := G) t).IsQueryBoundP (fun q => q.isRight = true) 1 ∧
      ¬ (oneQuery (G := G) t).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  constructor
  · simp [oneQuery]
  · simp [oneQuery]

/-- Membership in `supportWhen P` after an oracle query `t` requires an answer satisfying `P t`. -/
theorem mem_supportWhen_query_bind {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (P : (t : ι') → spec t → Prop) (t : ι') (mx : spec t → OracleComp spec α) (y : α) :
    y ∈ supportWhen P (liftM (OracleSpec.query t) >>= mx) ↔ ∃ u, P t u ∧ y ∈ supportWhen P (mx u) :=
  Iff.rfl

theorem supportWhen_pure {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (P : (t : ι') → spec t → Prop) (a : α) :
    supportWhen P (pure a : OracleComp spec α) = {a} := rfl

/-- Single-session SM oracle specification for `e2eSessionCodec`. -/
abbrev E2ESessG (ℓ : ℕ) := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes

/-- `corr-A`, encoded as a single `.bool` leaf. -/
def e2eCorrA (ℓ : ℕ) : (E2ESessG ℓ).Domain := .inr Party.A

theorem e2eSession_oneQuery_fits (ℓ B : ℕ) :
    AllGameQueriesFit B (e2eSessionCodec ℓ) (oneQuery (G := E2ESessG ℓ) (e2eCorrA ℓ)) :=
  oneQuery_fits _ B _ (by trivial)

theorem e2eSession_oneQuery_bound (ℓ : ℕ) :
    (oneQuery (G := E2ESessG ℓ) (e2eCorrA ℓ)).IsQueryBoundP (fun q => q.isRight = true) 1 ∧
      ¬ (oneQuery (G := E2ESessG ℓ) (e2eCorrA ℓ)).IsQueryBoundP (fun q => q.isRight = true) 0 :=
  oneQuery_bound _

/-- Global query-size bounds fail for `e2eSessionCodec`: a `deliver-A` query carrying `32 * (B + 1)`
ciphertext bytes exceeds block bound `B`. -/
theorem e2eSession_global_query_premise_false (ℓ B : ℕ) :
    ¬ ∀ t : (E2ESessG ℓ).Domain, (e2eSessionCodec ℓ).Q.Fits B ((e2eSessionCodec ℓ).qenc t) := by
  intro h
  have h1 : ((List.replicate (32 * (B + 1)) (0 : BitVec 8)).length + 32 - 1) / 32 ≤ B :=
    (h (.inl (.inl (.inr (Party.A, List.replicate (32 * (B + 1)) 0))))).2
  rw [List.length_replicate] at h1
  omega

/-- `DeliverForge` SM oracle specification for `fig8SmCodecDF`. -/
abbrev Fig8DFG (ℓ : ℕ) (Pt : Type) :=
  SM.specDF
    (SM.Construction.PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
    (SM.Construction.Header Pt × (ℕ × LibsignalCiphertextWithSalt32))

/-- `corr-A` in the Fig. 8 game, encoded as a single `.bool` leaf. -/
def fig8CorrA (ℓ : ℕ) (Pt : Type) : (Fig8DFG ℓ Pt).Domain := .inl (.inr Party.A)

theorem fig8DF_oneQuery_fits (ℓ : ℕ) (Pt : Type) (B : ℕ) :
    AllGameQueriesFit B (fig8SmCodecDF ℓ Pt) (oneQuery (G := Fig8DFG ℓ Pt) (fig8CorrA ℓ Pt)) :=
  oneQuery_fits _ B _ (by trivial)

theorem fig8DF_oneQuery_bound (ℓ : ℕ) (Pt : Type) :
    (oneQuery (G := Fig8DFG ℓ Pt) (fig8CorrA ℓ Pt)).IsQueryBoundP (fun q => q.isRight = true) 1 ∧
      ¬ (oneQuery (G := Fig8DFG ℓ Pt) (fig8CorrA ℓ Pt)).IsQueryBoundP
        (fun q => q.isRight = true) 0 :=
  oneQuery_bound _

theorem pqKeyInd_oneQuery_fits (S : SignalPqxdh.Setup) (B : ℕ) :
    AllGameQueriesFit B (pqKeyIndCodec S)
      (oneQuery (G := SignalPqxdh.keyIndSpec S) .revealDhSecrets) :=
  oneQuery_fits _ B _ (by trivial)

theorem pqKeyInd_oneQuery_bound (S : SignalPqxdh.Setup) :
    (oneQuery (G := SignalPqxdh.keyIndSpec S) .revealDhSecrets).IsQueryBoundP
        (fun q => SignalPqxdh.isGameQuery q = true) 1 ∧
      ¬ (oneQuery (G := SignalPqxdh.keyIndSpec S) .revealDhSecrets).IsQueryBoundP
        (fun q => SignalPqxdh.isGameQuery q = true) 0 := by
  constructor
  · simp [oneQuery, SignalPqxdh.isGameQuery]
  · simp [oneQuery, SignalPqxdh.isGameQuery]

theorem auth_oneQuery_fits (S : SignalPqxdh.Setup) (B : ℕ) :
    AllGameQueriesFit B (SignalPqxdh.Costed.authCodec S)
      (oneQuery (G := SignalPqxdh.authSpec S) .revealDhSecrets) :=
  oneQuery_fits _ B _ (by trivial)

theorem auth_oneQuery_bound (S : SignalPqxdh.Setup) :
    (oneQuery (G := SignalPqxdh.authSpec S) .revealDhSecrets).IsQueryBoundP
        (fun q => SignalPqxdh.isGameQuery q = true) 1 ∧
      ¬ (oneQuery (G := SignalPqxdh.authSpec S) .revealDhSecrets).IsQueryBoundP
        (fun q => SignalPqxdh.isGameQuery q = true) 0 := by
  constructor
  · simp [oneQuery, SignalPqxdh.isGameQuery]
  · simp [oneQuery, SignalPqxdh.isGameQuery]

end CryptoVerification.E2E.NonVacuity.RunLocalFits
