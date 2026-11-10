/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHAuthTraces

/-!
# Ordering-Bound Tightness for Composed PQXDH Authentication

Tightens each strict trace-index inequality `j < i` in `PQXDH.AuthenticationQuery` to
`j + gap < i` across `ResponderSessionAgreement` and the three `HandshakeAuthWasCompromised`
clauses. At `gap = 0` this coincides with `Composed.Security.Authentication`, whereas each positive
gap at the minimal witness distance `i - j` is refuted by a reachable composed trace.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHBounds

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (trBrokenDHB_bobDone
  trBrokenDHB_compromise_indices trBrokenDHB_reach trIKA_bobDone trIKA_compromise_indices
  trIKA_reach trSPKB_bobDone trSPKB_compromise_indices trSPKB_reach)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB spkB t8 t8_bobDone_at t8_reach)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHAuthTraces (Thm8Case
  handshakeAuthWasCompromised_iff_exists_thm8Case
  not_loggedBefore_gap_of_singleton t8_aliceDone_idx_eq t8_no_thm8Case
  trBrokenDHB_no_thm8Agreement trBrokenDHB_not_other_thm8Case trIKA_no_thm8Agreement
  trIKA_not_other_thm8Case trSPKB_no_thm8Agreement trSPKB_not_other_thm8Case)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman DY.PQKem
open DY.Libsignal.PQXDH
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security

/-- `LoggedBefore` strengthened to require an additive trace-index gap `j + gap < i`. -/
def LoggedBeforeGap (gap : Nat) (ev : PQXDHEvent) (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ j, tr.EventLoggedAt ev j ∧ j + gap < i

theorem loggedBeforeGap_zero (ev : PQXDHEvent) (i : Nat) (tr : ExecTrace) :
    LoggedBeforeGap 0 ev i tr ↔ PQXDH.LoggedBefore ev i tr :=
  Iff.rfl

def Thm8CaseGap (gIKA gSPK gDH : Nat) (b a : Participant) (ikA spk : Bytes)
    (i : Nat) (tr : ExecTrace) : Fin 3 → Prop
  | 0 => LoggedBeforeGap gIKA (PQXDHEvent.CompromisedIK a ikA) i tr
  | 1 => LoggedBeforeGap gSPK (PQXDHEvent.CompromisedSPK b spk) i tr
  | 2 => LoggedBeforeGap gDH PQXDHEvent.BrokenDH i tr

theorem thm8CaseGap_zero (b a : Participant) (ikA spk : Bytes)
    (i : Nat) (tr : ExecTrace) (k : Fin 3) :
    Thm8CaseGap 0 0 0 b a ikA spk i tr k ↔ Thm8Case b a ikA spk i tr k :=
  match k with
  | 0 => Iff.rfl
  | 1 => Iff.rfl
  | 2 => Iff.rfl

def Thm8ExcuseGap (gIKA gSPK gDH : Nat) (b a : Participant) (ikA spk : Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ k, Thm8CaseGap gIKA gSPK gDH b a ikA spk i tr k

theorem thm8ExcuseGap_zero (b a : Participant) (ikA spk : Bytes)
    (i : Nat) (tr : ExecTrace) :
    Thm8ExcuseGap 0 0 0 b a ikA spk i tr ↔ PQXDH.HandshakeAuthWasCompromised b a ikA spk i tr :=
  (exists_congr (thm8CaseGap_zero b a ikA spk i tr)).trans
    (handshakeAuthWasCompromised_iff_exists_thm8Case b a ikA spk i tr).symm

def Thm8AgreementGap (gap : Nat) (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ b' ikA' ikB' spk' opk' ek' ct' keys' j,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk opk' ek' ct' keys') j ∧
    j + gap < i ∧
    PQXDH.SameDHKey spk spk' ∧
    PQXDH.SameOPK opk opk'

theorem thm8AgreementGap_zero (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) :
    Thm8AgreementGap 0 a spk pqpk opk i tr ↔ PQXDH.ResponderSessionAgreement a spk pqpk opk i tr :=
  Iff.rfl

def AuthenticationQueryGap (gAg gIKA gSPK gDH : Nat) (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    Thm8AgreementGap gAg a spk pqpk opk i tr ∨
    Thm8ExcuseGap gIKA gSPK gDH b a ikA spk i tr

theorem authenticationQueryGap_zero (tr : ExecTrace) :
    AuthenticationQueryGap 0 0 0 0 tr ↔ PQXDH.AuthenticationQuery tr := by
  unfold AuthenticationQueryGap PQXDH.AuthenticationQuery
  refine forall_congr' fun b => forall_congr' fun a => forall_congr' fun ikB =>
    forall_congr' fun ikA => forall_congr' fun spk => forall_congr' fun pqpk =>
    forall_congr' fun opk => forall_congr' fun ek => forall_congr' fun ct =>
    forall_congr' fun keys => forall_congr' fun i => imp_congr_right fun _ => ?_
  exact or_congr (thm8AgreementGap_zero a spk pqpk opk i tr)
    (thm8ExcuseGap_zero b a ikA spk i tr)

/-- `Composed.Security.Authentication` with additive index gaps `(gAg, gIKA, gSPK, gDH)` on
agreement and the three compromise clauses. -/
def AuthenticationGap (gAg gIKA gSPK gDH : Nat) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    AuthenticationQueryGap gAg gIKA gSPK gDH tr

theorem authenticationGap_zero :
    AuthenticationGap 0 0 0 0 ↔ Authentication :=
  forall_congr' fun tr => imp_congr_right fun _ => authenticationQueryGap_zero tr

theorem not_AuthenticationGap_of_witness
    {gAg gIKA gSPK gDH : Nat} {tr : ExecTrace}
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes}
    {ek ct : Bytes} {keys : HandshakeKeys} {i : Nat}
    (hReach : tr.Reachable reachability)
    (hBob : tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i)
    (hNoAgree : ¬ Thm8AgreementGap gAg a spk pqpk opk i tr)
    (hNoCase : ∀ k : Fin 3, ¬ Thm8CaseGap gIKA gSPK gDH b a ikA spk i tr k) :
    ¬ AuthenticationGap gAg gIKA gSPK gDH := by
  intro hAuth
  rcases hAuth tr hReach b a ikB ikA spk pqpk opk ek ct keys i hBob with
    hAgree | ⟨k, hkCase⟩
  · exact hNoAgree hAgree
  · exact hNoCase k hkCase

/-- Tightening `j < i` to `j + 7 < i` in the `CompromisedIK` clause falsifies `Authentication`
(`trIKA`, `29 - 22 = 7`). -/
theorem not_AuthenticationGap_ikA : ¬ AuthenticationGap 0 7 0 0 := by
  refine not_AuthenticationGap_of_witness trIKA_reach trIKA_bobDone
    (trIKA_no_thm8Agreement _ _ _ _ _) fun k => ?_
  match k with
  | 0 =>
    rintro ⟨j, hj, hlt⟩
    exact not_loggedBefore_gap_of_singleton trIKA_compromise_indices rfl (by omega) j hj hlt
  | 1 => exact trIKA_not_other_thm8Case 1 (by decide)
  | 2 => exact trIKA_not_other_thm8Case 2 (by decide)

/-- Tightening `j < i` to `j + 7 < i` in the `CompromisedSPK` clause falsifies `Authentication`
(`trSPKB`, `29 - 22 = 7`). -/
theorem not_AuthenticationGap_spk : ¬ AuthenticationGap 0 0 7 0 := by
  refine not_AuthenticationGap_of_witness trSPKB_reach trSPKB_bobDone
    (trSPKB_no_thm8Agreement _ _ _ _ _) fun k => ?_
  match k with
  | 0 => exact trSPKB_not_other_thm8Case 0 (by decide)
  | 1 =>
    rintro ⟨j, hj, hlt⟩
    exact not_loggedBefore_gap_of_singleton trSPKB_compromise_indices rfl (by omega) j hj hlt
  | 2 => exact trSPKB_not_other_thm8Case 2 (by decide)

/-- Tightening `j < i` to `j + 7 < i` in the `BrokenDH` clause falsifies `Authentication`
(`trBrokenDHB`, `29 - 22 = 7`). -/
theorem not_AuthenticationGap_dh : ¬ AuthenticationGap 0 0 0 7 := by
  refine not_AuthenticationGap_of_witness trBrokenDHB_reach trBrokenDHB_bobDone
    (trBrokenDHB_no_thm8Agreement _ _ _ _ _) fun k => ?_
  match k with
  | 0 => exact trBrokenDHB_not_other_thm8Case 0 (by decide)
  | 1 => exact trBrokenDHB_not_other_thm8Case 1 (by decide)
  | 2 =>
    rintro ⟨j, hj, hlt⟩
    exact not_loggedBefore_gap_of_singleton trBrokenDHB_compromise_indices rfl (by omega) j hj hlt

/-- Tightening `j < i` to `j + 20 < i` in `ResponderSessionAgreement` falsifies `Authentication`
(`HonestSession.t8`, `47 - 27 = 20`). -/
theorem not_AuthenticationGap_agreement : ¬ AuthenticationGap 20 0 0 0 := by
  refine not_AuthenticationGap_of_witness t8_reach t8_bobDone_at ?_ fun k => ?_
  · rintro ⟨b', ikA', ikB', spk', opk', ek', ct', keys', j, hEv, hlt, _⟩
    have hj := t8_aliceDone_idx_eq hEv
    omega
  · exact mt (thm8CaseGap_zero "bob" "alice" (dhPk ikA) (dhPk spkB) 47 t8 k).mp
      (t8_no_thm8Case k)

end Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHBounds
