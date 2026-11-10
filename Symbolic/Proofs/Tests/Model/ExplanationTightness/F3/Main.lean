/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Statement
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Secrecy

/-!
# Replay-Aliasing Tightness for `HandshakeRootCompromised`

Proves `not_handshakeRootOverExcuse` (`¬ HandshakeRootOverExcuse`) and
`oldOverExcuses_replay_witness` (`OldOverExcusesReplayWitness`) on the concrete replay trace
`fTr`. Under the session-scoped `HandshakeRootCompromised`, cross-handshake key-value aliasing
never excuses a key shared with an unexcused handshake, whereas the existential baseline
`HandshakeRootCompromised_old` excuses Alice's uncompromised message-0 seed `mkA` on `fTr`.
-/

@[expose] public section

set_option autoImplicit false

open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (TestTracePredicates mkTestTracePredicates FSQueryP PCSQueryP fsQuery_iff_test pcsQuery_iff_test)

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Main

open Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Secrecy (fTr_not_knows_mkA mkA)
open Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Statement (FSExcuse
  HandshakeRootOverExcuse OldOverExcusesReplayWitness tracePredicatesOld)
open Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Trace (derivesChain_stA0
  derivesMsgKey_stA0 fTr fTr_messageKeyA_at fTr_no_exposed fTr_no_ikOrDH fTr_reach
  handshakeKeysAt_fTr handshakeKeysAt_fTr_27 handshakeRootCompromised_old_fTr not_excused_27)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (keys1 stA0)

open DY
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (TREvent kdfCk)
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH (HandshakeKeysAt HandshakeWasCompromisedAt)

theorem fTr_messageKey_mkA : (mkTestTracePredicates fTr).MessageKey mkA :=
  ⟨_, _, _, _, _, _, ⟨35, fTr_messageKeyA_at⟩⟩

/-- Cross-handshake key-value aliasing never excuses an unexcused session on any reachable trace. -/
theorem not_handshakeRootOverExcuse : ¬ HandshakeRootOverExcuse := by
  rintro ⟨tr, _, mk, keys, j₁, j₂, s, ck, _, hhk₂, hne₂, _, _, _, _, _, _, ⟨_, hall⟩, _⟩
  exact hne₂ (hall keys j₂ hhk₂ (.inl rfl))

private theorem fTr_compromised_old_rk : (tracePredicatesOld fTr).Compromised keys1.rk :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl handshakeRootCompromised_old_fTr)))))

private theorem fTr_fsExcuse_old_mkA : FSExcuse (tracePredicatesOld fTr) mkA :=
  Or.inr (Or.inr ⟨keys1.rk, stA0.cks, derivesChain_stA0, derivesMsgKey_stA0, fTr_compromised_old_rk⟩)

private theorem not_compromised_fTr (k : Bytes) :
    ¬ (mkTestTracePredicates fTr).Compromised k := by
  rintro (⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, n, i, h⟩ | ⟨s, n, i, h⟩ | ⟨s, n, i, h⟩ |
      ⟨⟨keys, j, hk, hkk⟩, hall⟩ | ⟨_, h⟩)
  · exact fTr_no_exposed h rfl
  · exact fTr_no_exposed h rfl
  · exact fTr_no_exposed h rfl
  · exact fTr_no_exposed h rfl
  · exact fTr_no_exposed h rfl
  · obtain rfl := handshakeKeysAt_fTr hk
    exact not_excused_27 (hall keys1 27 handshakeKeysAt_fTr_27 hkk)
  · exact fTr_no_ikOrDH h rfl

private theorem not_fsExcuse_fTr (mk : Bytes) : ¬ FSExcuse (mkTestTracePredicates fTr) mk := by
  rintro (h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩)
  all_goals exact not_compromised_fTr _ h

/-- On `fTr`, the existential baseline `tracePredicatesOld` excuses `mkA` even though `mkA` is
attacker-unknown and unexcused under `mkTestTracePredicates`. -/
theorem oldOverExcuses_replay_witness : OldOverExcusesReplayWitness :=
  ⟨fTr, fTr_reach, mkA, fTr_messageKey_mkA, fTr_not_knows_mkA, fTr_fsExcuse_old_mkA,
    not_fsExcuse_fTr mkA⟩

end Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Main
