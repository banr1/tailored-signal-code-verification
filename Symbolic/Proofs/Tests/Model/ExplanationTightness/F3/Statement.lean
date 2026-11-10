/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
public import Symbolic.Specifications.Security.Model

/-!
# Replay-Aliasing Tightness Statements for `HandshakeRootCompromised`

States `HandshakeRootOverExcuse` (whether cross-handshake key-value aliasing can excuse an
attacker-unknown message key of an unexcused session under `mkTestTracePredicates`) and
`OldOverExcusesReplayWitness` (strictness of the session-scoped `HandshakeRootCompromised` over the
existential baseline `HandshakeRootCompromised_old`). Both propositions are discharged in
`F3/Main.lean`.
-/

@[expose] public section

set_option autoImplicit false

open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (TestTracePredicates mkTestTracePredicates FSQueryP PCSQueryP fsQuery_iff_test pcsQuery_iff_test)

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Statement

open DY
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (TREvent SessionInfo DerivesMsgKey DerivesChain)
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH (HandshakeKeys HandshakeKeysAt HandshakeWasCompromisedAt)

/-- The excuse that `FSQueryP P` grants for the message-key seed `mk` (the conclusion of
`FSQuery`). -/
def FSExcuse (P : TestTracePredicates) (mk : Bytes) : Prop :=
  P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk)

theorem fsQuery_iff (P : TestTracePredicates) :
    FSQueryP P ↔ ∀ mk, P.MessageKey mk → P.AttackerKnows mk → FSExcuse P mk :=
  Iff.rfl

/-- Whether some reachable trace has an attacker-unknown message-key seed `mk` from an unexcused
session at `j₂` that `FSExcuse (mkTestTracePredicates tr)` nevertheless excuses via
`HandshakeRootCompromised tr keys.rk` because an excused handshake at `j₁ ≠ j₂` derived the same
`keys`. -/
def HandshakeRootOverExcuse : Prop :=
  ∃ tr : ExecTrace, tr.Reachable reachability ∧
    ∃ (mk : Bytes) (keys : HandshakeKeys) (j₁ j₂ : Nat) (s : SessionInfo) (ck : Bytes),
      tr.EventLogged (ComposedEvent.HandshakeSession s j₂) ∧
      HandshakeKeysAt tr j₂ keys ∧ ¬ HandshakeWasCompromisedAt tr j₂ ∧
      (∃ dir pqSalt n i parentStateIdx,
        tr.EventLogged
          (TREvent.MessageKey s dir mk pqSalt n i parentStateIdx)) ∧
      (mkTestTracePredicates tr).MessageKey mk ∧
      ¬ (mkTestTracePredicates tr).AttackerKnows mk ∧
      FSExcuse (mkTestTracePredicates tr) mk ∧
      DerivesChain keys.rk ck ∧ DerivesMsgKey ck mk ∧ HandshakeRootCompromised tr keys.rk ∧
      j₁ ≠ j₂ ∧ HandshakeKeysAt tr j₁ keys ∧ HandshakeWasCompromisedAt tr j₁

/-! ## Existential Baseline -/

/-- Existential baseline predicate that excuses `k` whenever at least one handshake deriving `k` as
its initial root or chain key is excused. -/
def HandshakeRootCompromised_old (tr : ExecTrace) (k : Bytes) : Prop :=
  ∃ keys j, HandshakeKeysAt tr j keys ∧ HandshakeWasCompromisedAt tr j ∧ (k = keys.rk ∨ k = keys.ck)

/-- `mkTestTracePredicates tr` with `HandshakeRootCompromised_old` in place of
`HandshakeRootCompromised`. -/
def tracePredicatesOld (tr : ExecTrace) : TestTracePredicates :=
  let P := mkTestTracePredicates tr
  { P with
    Compromised := fun k =>
      (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
      (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
      (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
      (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
      (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i)) ∨
      HandshakeRootCompromised_old tr k ∨
      (P.HonestDH k ∧ tr.EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH) }

/-- Existence of a reachable trace and an attacker-unknown message-key seed `mk` excused by
`tracePredicatesOld` and unexcused by `mkTestTracePredicates`. -/
def OldOverExcusesReplayWitness : Prop :=
  ∃ tr : ExecTrace, tr.Reachable reachability ∧
    ∃ mk : Bytes,
      (mkTestTracePredicates tr).MessageKey mk ∧
      ¬ (mkTestTracePredicates tr).AttackerKnows mk ∧
      FSExcuse (tracePredicatesOld tr) mk ∧
      ¬ FSExcuse (mkTestTracePredicates tr) mk

end Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Statement
