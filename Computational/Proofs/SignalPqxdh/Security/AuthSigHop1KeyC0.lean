/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdPreSample

/-!
# One-key `Auth` bad-signature hop: shared real-side definitions

**Checked by Lean.** Defines the frozen one-key `Exact` provenance oracle with pre-sampled target
identity scalar (`pqxdhAuthSigPreImpl1Key`), the active-phase invariant `authSigGood1Key`, and the
`NoOpk` to `Exact` rewrite for `authSig1KeyPerKBound`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp

namespace Proofs.SignalPqxdh.Security

/-- Frozen one-key `Exact` provenance oracle with principal `k`'s identity scalar pre-sampled. -/
noncomputable def pqxdhAuthSigPreImpl1Key (k : ℕ) (optSk : Option Bytes) (S : Setup)
    (P : Primitives) : QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) :=
  freezeImpl AuthState.hasWonAuth (fun _ => .noneResp) (fun q =>
    match q with
    | .initPrin u => fgPreAuthInitPrin1Key true k optSk S P u
    | q => pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceExact P) q)

theorem pqxdhAuthSigPreImpl1Key_none (k : ℕ) (S : Setup) (P : Primitives) :
    pqxdhAuthSigPreImpl1Key k none S P =
      pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P) := by
  funext q
  unfold pqxdhAuthSigPreImpl1Key pqxdhAuthWithProvFrozenImpl1Key
  cases q <;> rfl

theorem pqxdhAuthSigPreImpl1Key_of_not_initPrin (k : ℕ) (optSk : Option Bytes) (S : Setup)
    (P : Primitives) (q : AuthQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthSigPreImpl1Key k optSk S P q =
      pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P) q := by
  unfold pqxdhAuthSigPreImpl1Key pqxdhAuthWithProvFrozenImpl1Key freezeImpl
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem badPeersAuth_mapAuthSessions_eraseOpk {S : Setup} (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := eraseOpkTriples (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    badPeersAuth (mapAuthSessions mapEntry st) = badPeersAuth st := by
  intro mapEntry
  unfold badPeersAuth mapAuthSessions
  dsimp only
  rw [List.filter_map, List.map_map]
  rfl

theorem hasBadSigAuthAt_mapAuthSessions_eraseOpk (S : Setup) (P : Primitives) (k : ℕ)
    (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := eraseOpkTriples (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    hasBadSigAuthAt S P k (mapAuthSessions mapEntry st) = hasBadSigAuthAt S P k st := by
  intro mapEntry
  unfold hasBadSigAuthAt SigGameLens.badAt
  dsimp only [authSigLens]
  rw [badPeersAuth_mapAuthSessions_eraseOpk st]
  rfl

theorem authSig1KeyPerK_lhs_noOpk_eq_exact (S : Setup) (P : Primitives) (k : ℕ)
    (A : AuthAdversary S) :
    (runAuthWithProvFrozen1Key (checkBundleProvenanceNoOpk P) S P A >>= fun (_, _, finalSt) =>
      pure (hasBadSigAuthAt S P k finalSt)) =
    (runAuthWithProvFrozen1Key (checkBundleProvenanceExact P) S P A >>= fun (_, _, finalSt) =>
      pure (hasBadSigAuthAt S P k finalSt)) := by
  rw [runAuthWithProvFrozen1Key_eq_map S P eraseOpkTriples
        (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P) A,
      bind_map_left]
  refine bind_congr (fun ⟨secb, b', st⟩ => ?_)
  dsimp only
  rw [hasBadSigAuthAt_mapAuthSessions_eraseOpk]

/-- Active-phase invariant of the real side of the one-key `Auth` signature coupling. -/
def authSigGood1Key (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes) (st : AuthState S) : Prop :=
  ValidPrincipals S st.principals ∧
  (∀ e, (k, e) ∈ st.principals →
    e.secIKAsign = sk ∧ e.ikSignPk = P.sigPkGen sk ∧ e.corrupted = false) ∧
  CleanPeers S P k st.principals (badPeersAuth st)

theorem authSigGood1Key_empty (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes) (secb : Bool) :
    authSigGood1Key S P k sk (AuthState.empty S secb) :=
  ⟨⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
    fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩

theorem hasBadSigAuthAt_eq_false_of_good (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes)
    (st : AuthState S) (h : authSigGood1Key S P k sk st) : hasBadSigAuthAt S P k st = false := by
  unfold hasBadSigAuthAt SigGameLens.badAt
  dsimp only [authSigLens]
  rw [any_peerPartyIdx_eq_false_of_cleanPeers S P k st.principals (badPeersAuth st) h.2.2]

end Proofs.SignalPqxdh.Security
